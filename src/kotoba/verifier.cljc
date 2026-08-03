(ns kotoba.verifier
  #?(:clj (:require [clojure.set :as set]
                    [kotoba.artifact.core :as artifact]
                    [kotoba.native.aarch64 :as aarch64]
                    [kotoba.native.x86-64 :as x86-64]
                    [kotoba.kir.compatibility :as compatibility-profile]
                    [kotoba.kir :as ir]
                    [kotoba.kir.target :as target-profile])
     :cljs (:require [clojure.set :as set]
                     [kotoba.artifact.core :as artifact]
                     [kotoba.native.aarch64 :as aarch64]
                     [kotoba.native.x86-64 :as x86-64]
                     [kotoba.kir.cljs-i64 :as i64]
                     [kotoba.kir.compatibility :as compatibility-profile]
                     [kotoba.kir :as ir]
                     [kotoba.kir.target :as target-profile])))

(defn- reject! [message data]
  (throw (ex-info message (assoc data :phase :verify))))

(def target-contracts
  {:x86_64-kotoba-v1 {:lowering :runtime-sysv-v1 :emit x86-64/emit-program}
   :aarch64-kotoba-v1 {:lowering :runtime-aapcs64-v1 :emit aarch64/emit-program}})

(def ^:private artifact-fields
  #{:format :target :target-profile :value :kir-sha256 :lowering :fuel-abi :context-abi
    :effects :limits :code :program :exports :compatibility :sha256})

(def max-functions 1024)
(def max-expression-nodes 50000)
(def max-lowered-nodes 100000)
(def ^:private max-depth 256)
(def ^:private max-bindings 4096)
(def ^:private max-parameters 5)
(def ^:private max-symbol-chars 128)
;; Independently re-derived from `kotoba.compiler.frontend/arithmetic` ON
;; PURPOSE -- this verifier must not import the producer's own sets, or it
;; would ratify whatever the producer decided. The cost of that independence is
;; that the two can drift, and they did: `bit-or` was added to the frontend, to
;; `kotoba.kir`'s evaluator, and to the x86-64 backend (ADR-2607254600 D2), but
;; never here. The drift was in the SAFE direction -- this verifier runs on
;; every compile and every execution, so it rejected `bit-or` rather than
;; admitting something unchecked -- which is exactly why it went unnoticed:
;; nothing broke, `bit-or` was simply dead on every native target.
(def ^:private arithmetic '#{+ - * quot bit-xor bit-and bit-or})
;; `kotoba.compiler.frontend/i64-operations`, independently re-derived for the
;; same reason `arithmetic` is. Held separately because the shift forms carry an
;; operand restriction no other arithmetic has: the count must be an integer
;; LITERAL in [0,63]. That restriction is load-bearing, not cosmetic -- it is
;; the only reason the native backends may lower these onto CL / x1 without
;; emitting a range check, since the hardware would otherwise silently truncate
;; the count mod 64 where `kotoba.kir`'s evaluator traps. A verifier that
;; admitted a non-literal or out-of-range count would therefore admit an
;; artifact whose code and whose sealed oracle value disagree.
(def ^:private i64-operations '{bit-not 1 i64-shift-left 2 i64-shift-right 2 u64-shift-right 2})
;; `kotoba.compiler.frontend/i32-operations`, independently re-derived like the
;; sets above. `xorshift32` is absent on purpose: the frontend desugars it into
;; a `let` over these, so it never survives into KIR.
;;
;; The shifts carry the same kind of operand restriction the i64 shifts do, one
;; width down: the count must be an integer LITERAL in [0,31]. It is
;; load-bearing for the same reason -- it is why the native backends may lower
;; these onto CL / w1 without emitting a mask, since the hardware truncates the
;; count mod 32 exactly where `kotoba.kir`'s `checked-shift32` traps.
(def ^:private i32-operations
  '{i32-wrap 1 u32-wrap 1 i32-wrapping-add 2 i32-wrapping-mul 2 i32-xor 2
    i32-shift-left 2 i32-shift-right 2 u32-shift-right 2})
(def ^:private i32-shifts '#{i32-shift-left i32-shift-right u32-shift-right})
(def ^:private i64-shifts '#{i64-shift-left i64-shift-right u64-shift-right})
(def ^:private comparisons '#{= < > <= >=})
(def ^:private heap-operations '{pair 2 pair-first 1 pair-second 1})
(def ^:private kgraph-operations '{kgraph-assert! 3 kgraph-get 2 kgraph-count 1 kgraph-entity-at 2})
;; `string-substring` is admitted here as the target-independent operation it
;; is. The narrowing to an all-ASCII literal operand lives in the native
;; backends, not in this table: a shape they cannot emit is reported by them as
;; not implemented, which is accurate and fail-closed, whereas encoding a
;; backend restriction here would make this verifier ratify one target's
;; limits.
(def ^:private string-operations
  '{string-byte-length 1 string=? 2 string-concat 2 string-substring 3 string-code-point-at 2
    keyword-name 1 keyword-from-string 1})
(def ^:private tagged-i64-operations
  '{option-some 1 option-none 0 option-some? 1 option-value 2
    result-ok 1 result-err 1 result-ok? 1 result-value 2 result-error 2})
(def ^:private xml-operations
  '{xml-path-count 2 xml-name-count 2 xml-name-text 3 xml-path-text 3 xml-path-attr 4})
(def ^:private decimal-operations '{decimal-f64-parse 1 decimal-f64x3-parse 1})
(def ^:private string-literal-byte-limit 4096)
(def ^:private max-record-fields 32)

;; Independently re-derived from `kotoba.kir/native-scalar-record-type?`
;; ON PURPOSE -- this verifier is a from-scratch re-check of the embedded
;; KIR, so it must never call into the compiler code being verified (same
;; reasoning already documented at every other op-family in this file: none
;; of `arithmetic`/`heap-operations`/`kgraph-operations`/... share a helper
;; with the emitters/admission they cross-check either).
;; What a record field or variant payload may hold on native: whatever fits in
;; ONE WORD. Independently re-derived like every other set in this file.
;;
;; `:string` belongs because a string value on native already IS a one-word
;; `pair(offset,length)` handle -- the same width as an `:i64` -- so it needs no
;; representation the slot machinery does not already have.
;;
;; `:f64` is excluded because the compiler rejects any f64 on native
;; independently of records; `:keyword` because the backends have no keyword
;; representation at all.
(def ^:private native-word-field-types #{:i64 :bool :string :keyword})

(declare native-scalar-record-type?)

(defn- native-scalar-record-type? [type]
  (and (vector? type) (= 3 (count type)) (= :record (first type))
       (keyword? (second type)) (some? (namespace (second type)))
       (vector? (nth type 2)) (seq (nth type 2)) (<= (count (nth type 2)) max-record-fields)
       (every? (fn [field]
                 (and (vector? field) (= 2 (count field)) (keyword? (first field))
                      ;; A record field may itself be a record: the backends
                      ;; flatten it into the enclosing record's slots,
                      ;; recursively, so nothing gains a runtime representation.
                      (or (contains? native-word-field-types (second field))
                          (native-scalar-record-type? (second field)))))
               (nth type 2))
       (= (count (nth type 2)) (count (distinct (map first (nth type 2)))))))

;; Independently re-derived from `kotoba.kir/native-scalar-variant-
;; type?` ON PURPOSE, same reasoning as `native-scalar-record-type?`'s own
;; comment immediately above (ADR 0063).
(def ^:private max-variant-cases 32)
(defn- native-scalar-variant-type? [type]
  (and (vector? type) (= 3 (count type)) (= :variant (first type))
       (keyword? (second type)) (some? (namespace (second type)))
       (vector? (nth type 2)) (seq (nth type 2)) (<= (count (nth type 2)) max-variant-cases)
       (every? (fn [case-entry]
                 (and (vector? case-entry) (= 2 (count case-entry)) (keyword? (first case-entry))
                      ;; A case payload may itself be a record, which the
                      ;; backends flatten into the dispatch's payload slots.
                      (or (contains? native-word-field-types (second case-entry))
                          (native-scalar-record-type? (second case-entry)))))
               (nth type 2))
       (= (count (nth type 2)) (count (distinct (map first (nth type 2)))))))

(defn- native-word-value-type?
  "Independent verifier copy of the recursive one-word native value slice."
  ([type] (native-word-value-type? type 0))
  ([type depth]
   (and (<= depth 8)
        (or (contains? #{:i64 :bool :string} type)
            (and (vector? type)
                 (case (first type)
                   :option (and (= 2 (count type))
                                (native-word-value-type? (second type) (inc depth)))
                   :result (and (= 3 (count type))
                                (native-word-value-type? (second type) (inc depth))
                                (native-word-value-type? (nth type 2) (inc depth)))
                   false))))))

;; Mirrors `kotoba.wasm.core`'s `utf8` -- `.getBytes` is
;; JVM-only, cljs has no `String`/`Charset`; `TextEncoder` is the
;; UTF-8-safe equivalent.
(defn- utf8-byte-count [s]
  #?(:clj (alength (.getBytes ^String s "UTF-8"))
     :cljs (.-length (.encode (js/TextEncoder.) s))))

(defn- valid-name? [value]
  (and (simple-symbol? value) (<= (count (name value)) max-symbol-chars)))

;; Same bigint-recognition guard `verify-expr!` needs (see its own
;; comment): a cap-id straight from a KIR effect is a cljs `bigint`, which
;; `integer?` alone does not reliably recognize.
(defn- valid-effect? [effect]
  (and (vector? effect) (= 2 (count effect)) (= :cap/call (first effect))
       #?(:clj (integer? (second effect)) :cljs (or (i64/bigint-value? (second effect)) (integer? (second effect))))
       (<= 0 (second effect) 255)))

(defn- bounded-sum [values]
  (reduce (fn [total value] (min (inc max-lowered-nodes) (+ total value)))
          0 values))

(defn- lowered-cost [form env]
  (cond
    ;; Same bigint-recognition guard as `verify-expr!` below (see its own
    ;; comment) -- `form` here walks the same KIR expression tree.
    #?(:clj (integer? form) :cljs (or (i64/bigint-value? form) (integer? form)))
    1
    (string? form) 1
    ;; A keyword literal, reachable the same way a string one is -- as a record
    ;; field or variant payload value. Costed the same flat 1: on native it
    ;; lowers to the same one-word handle a string literal does.
    (keyword? form) 1
    ;; A bare literal `true`/`false` (only reachable via a record field
    ;; value, see `verify-expr!`'s own comment below) -- costed the same
    ;; flat 1 as any other scalar literal.
    (boolean? form) 1
    (symbol? form) (get env form 1)
    ;; `record-new`/`record-get`'s FIRST argument is a compile-time type
    ;; descriptor VECTOR (e.g. `[:record :kw [[:field :type] ...]]`), not a
    ;; KIR expression -- the generic `:else` branch below would otherwise
    ;; recurse `lowered-cost` into it as an ordinary arg and crash trying to
    ;; sequentially destructure a bare keyword (`(let [[op & args] :kw])`
    ;; throws, keywords are not seqable), so both ops are special-cased here
    ;; to skip the descriptor and cost only the actual value expressions.
    (and (seq? form) (= 'record-new (first form)))
    (let [[_ _type & values] form]
      (bounded-sum (cons 1 (map #(lowered-cost % env) values))))
    (and (seq? form) (= 'record-get (first form)))
    (let [[_ _type value _field] form]
      (bounded-sum [1 (lowered-cost value env)]))
    ;; `variant-new`/`variant-match`'s FIRST argument is likewise a compile-
    ;; time type descriptor, not a KIR expression -- same reasoning as
    ;; `record-new`/`record-get` immediately above (ADR 0063). `variant-
    ;; match`'s branches are `[tag binder body]` triples; only `body` costs
    ;; anything (mirrors `let`'s own env-threading just above), each binder
    ;; is scoped to its own branch only (they do not see each other).
    (and (seq? form) (= 'variant-new (first form)))
    (let [[_ _type _tag payload] form]
      (bounded-sum [1 (lowered-cost payload env)]))
    (and (seq? form) (= 'variant-match (first form)))
    (let [[_ _type value branches] form]
      (bounded-sum (list* 1 (lowered-cost value env)
                          (map (fn [[_tag binder body]] (lowered-cost body (assoc env binder 1)))
                               branches))))
    (and (seq? form) (= 'typed-cap-call (first form)))
    (let [[_ _cap-id _request-type _result-type request] form]
      (bounded-sum [1 (lowered-cost request env)]))
    (and (seq? form)
         (contains? '#{option-some-of option-some?-of
                       result-ok-of result-err-of result-ok?-of}
                    (first form)))
    (let [[_ _type value] form]
      (bounded-sum [1 (lowered-cost value env)]))
    (and (seq? form) (= 'option-none-of (first form))) 1
    (and (seq? form)
         (contains? '#{option-value-of result-value-of result-error-of}
                    (first form)))
    (let [[_ _type value fallback] form]
      (bounded-sum [1 (lowered-cost value env) (lowered-cost fallback env)]))
    (and (seq? form) (= 'option-match (first form)))
    (let [[_ _type value none-body binder some-body] form]
      (bounded-sum [1 (lowered-cost value env)
                    (lowered-cost none-body env)
                    (lowered-cost some-body (assoc env binder 1))]))
    (and (seq? form) (= 'result-match-of (first form)))
    (let [[_ _type value ok-binder ok-body err-binder err-body] form]
      (bounded-sum [1 (lowered-cost value env)
                    (lowered-cost ok-body (assoc env ok-binder 1))
                    (lowered-cost err-body (assoc env err-binder 1))]))
    :else
    (let [[op & args] form]
      (if (= op 'let)
        (let [[bindings body] args
              env' (reduce (fn [current [name value]]
                             (assoc current name (lowered-cost value current)))
                           env (partition 2 bindings))]
          (lowered-cost body env'))
        (bounded-sum (cons 1 (map #(lowered-cost % env) args)))))))

(declare verify-expr!)

;; `locals` maps each name to the record schema it was bound with, or nil. It
;; used to be a set of names, which was enough while a record could only ever
;; appear as a directly-nested `record-new` under its own `record-get`: there
;; was nothing about a local worth remembering. Admitting a LET-BOUND record
;; means the projection has to be checkable against what the name was bound
;; with, which a set cannot answer.
;;
;; Re-derived here rather than trusted: the schema is only remembered when the
;; bound value really is a `record-new` this verifier would itself admit.
(defn- record-new-schema [value]
  (when (and (seq? value) (= 'record-new (first value))
             (native-scalar-record-type? (second value)))
    (second value)))

(declare record-schema-of)

;; Declared result type per function, for resolving a record that arrives boxed
;; across a call boundary. Bound once per program by `verify-program!`.
(def ^:dynamic *call-results* {})

;; The record schema a form denotes, or nil. Three shapes reach here: a direct
;; `record-new`, a local bound to one, and -- once a record field may itself be
;; a record -- a `record-get` selecting such a field, whose schema is read off
;; the OUTER type's own field list rather than tracked separately.
;;
;; That last case is what makes a chained projection verifiable without the
;; intermediate record ever becoming a value.
(defn- record-schema-of [form locals]
  (cond
    (and (seq? form) (= 'record-new (first form))) (second form)
    (symbol? form) (get locals form)
    ;; A call whose declared result is a record: the operand arrived boxed.
    (and (seq? form) (simple-symbol? (first form)) (contains? *call-results* (first form)))
    (let [r (get *call-results* (first form))]
      (when (native-scalar-record-type? r) r))
    (and (seq? form) (= 'record-get (first form)) (= 4 (count form)))
    (let [[_ type value field] form]
      (when (= type (record-schema-of value locals))
        (let [field-type (second (first (filter #(= field (first %)) (nth type 2))))]
          (when (native-scalar-record-type? field-type) field-type))))
    :else nil))

(defn- verify-bindings! [bindings locals signatures depth nodes facts]
  (when-not (and (vector? bindings) (even? (count bindings))
                 (<= (quot (count bindings) 2) max-bindings))
    (reject! "runtime KIR let bindings rejected" {}))
  (let [names (take-nth 2 bindings)]
    (when-not (= (count names) (count (distinct names)))
      (reject! "runtime KIR duplicate binding rejected" {})))
  (loop [pairs (partition 2 bindings) env locals]
    (if-let [[name value] (first pairs)]
      (do
        (when-not (valid-name? name)
          (reject! "runtime KIR local name rejected" {:name name}))
        (verify-expr! value env signatures (inc depth) nodes facts)
        (recur (next pairs) (assoc env name (record-new-schema value))))
      env)))

(defn- verify-expr! [form locals signatures depth nodes facts]
  (when (> (vswap! nodes inc) max-expression-nodes)
    (reject! "runtime KIR expression budget exhausted" {}))
  (when (> depth max-depth)
    (reject! "runtime KIR expression depth rejected" {:depth depth}))
  (cond
    ;; `integer?` alone does not reliably recognize a cljs `bigint` (see
    ;; `kotoba.kir.cljs-i64`'s own namespace docstring) -- mirrors
    ;; `kotoba.wasm.core`'s identical dispatch guard.
    #?(:clj (integer? form) :cljs (or (i64/bigint-value? form) (integer? form)))
    (when-not #?(:clj (<= Long/MIN_VALUE form Long/MAX_VALUE)
                 :cljs (i64/in-i64-range? (i64/->bigint form)))
      (reject! "runtime KIR integer is outside i64" {:value form}))

    (symbol? form)
    (when-not (contains? locals form)
      (reject! "runtime KIR contains an unbound symbol" {:symbol form}))

    ;; A bare literal `true`/`false` -- the only source of a genuine
    ;; `:bool`-typed VALUE in this frontend's type system (every comparison,
    ;; including `=`, always yields `:i64`; see `ir/only-string-and-scalar-
    ;; record-typed-features?`'s own comment), reachable only as a
    ;; `record-new` field value or generic option/result payload under this
    ;; increment's admission. Always
    ;; valid; no bound to check.
    (boolean? form) nil

    (string? form)
    (when-not (<= (utf8-byte-count form) string-literal-byte-limit)
      (reject! "runtime KIR string literal exceeds byte limit" {:bytes (utf8-byte-count form)}))

    ;; A keyword literal is a value, carried on native as the same one-word
    ;; handle a string is, over its PRINTED text -- so the same byte bound
    ;; applies, measured over that text rather than over the name alone.
    (keyword? form)
    (when-not (<= (utf8-byte-count (str form)) string-literal-byte-limit)
      (reject! "runtime KIR keyword literal exceeds byte limit"
               {:bytes (utf8-byte-count (str form))}))

    (seq? form)
    (let [[op & args] form]
      (when-not (simple-symbol? op)
        (reject! "runtime KIR computed call rejected" {:operation op}))
      (cond
        (= op 'let)
        (let [[bindings & body] args]
          (when-not (= 1 (count body))
            (reject! "runtime KIR let arity rejected" {}))
          (verify-expr! (first body)
                        (verify-bindings! bindings locals signatures depth nodes facts)
                        signatures (inc depth) nodes facts))

        (= op 'if)
        (do
          (when-not (= 3 (count args)) (reject! "runtime KIR if arity rejected" {}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (= op 'do)
        (do
          (when (empty? args) (reject! "runtime KIR do arity rejected" {}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (= op 'cap-call)
        (let [[cap-id value :as call-args] args]
          (when-not (and (= 2 (count call-args))
                        #?(:clj (integer? cap-id) :cljs (or (i64/bigint-value? cap-id) (integer? cap-id)))
                        (<= 0 cap-id 255))
            (reject! "runtime KIR capability call rejected" {}))
          (vswap! facts update :effects conj [:cap/call cap-id])
          (verify-expr! value locals signatures (inc depth) nodes facts))

        (= op 'typed-cap-call)
        (let [[cap-id request-type result-type request :as call-args] args]
          (when-not (and (= 4 (count call-args))
                         #?(:clj (integer? cap-id)
                            :cljs (or (i64/bigint-value? cap-id) (integer? cap-id)))
                         (<= 0 cap-id 255)
                         (contains? #{[:i64 :i64] [:string :string]
                                      [:option-i64 :option-i64]
                                      [:result-i64 :result-i64]}
                                    [request-type result-type]))
            (reject! "runtime KIR typed capability call rejected" {}))
          (vswap! facts update :effects conj [:cap/call cap-id])
          (verify-expr! request locals signatures (inc depth) nodes facts))

        (contains? arithmetic op)
        (do
          ;; The strictly-binary set, mirroring the frontend's own arity gate.
          ;; `bit-or` belongs here for the same reason its siblings do: `+`/`-`/
          ;; `*` fold over any number of operands, the rest do not.
          (when (or (empty? args) (and (contains? '#{quot bit-xor bit-and bit-or} op) (not= 2 (count args))))
            (reject! "runtime KIR arithmetic arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        ;; `bool-not` takes one operand and yields the same :bool the
        ;; comparisons do. Independently re-derived like every set beside it;
        ;; the rest of `typed-safe-value-operations` (option/result) is handled
        ;; by its own cases further down.
        (= op 'bool-not)
        (do
          (when-not (= 1 (count args))
            (reject! "runtime KIR bool-not arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? i32-operations op)
        (do
          (when-not (= (get i32-operations op) (count args))
            (reject! "runtime KIR i32 operation arity rejected" {:operation op}))
          (when (and (contains? i32-shifts op)
                     (not (and (integer? (second args)) (<= 0 (second args) 31))))
            (reject! "runtime KIR i32 shift count rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? i64-operations op)
        (do
          (when-not (= (get i64-operations op) (count args))
            (reject! "runtime KIR i64 operation arity rejected" {:operation op}))
          ;; Re-derived from the frontend's own gate rather than trusted from
          ;; it. `integer?` is the right predicate on both runtimes here: an
          ;; out-of-range or non-literal count is what must be caught, and a
          ;; count in [0,63] is small enough that no bigint representation
          ;; question arises.
          (when (and (contains? i64-shifts op)
                     (not (and (integer? (second args)) (<= 0 (second args) 63))))
            (reject! "runtime KIR i64 shift count rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? comparisons op)
        (do
          (when-not (= 2 (count args))
            (reject! "runtime KIR comparison arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (= op 'record-new)
        (let [[type & values] args
              fields (when (native-scalar-record-type? type) (nth type 2))]
          (when-not (and fields (= (count fields) (count values)))
            (reject! "runtime KIR record construction rejected" {:operation op}))
          (doseq [arg values] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        ;; The codegen backends (`emit-record-get-of-new` in both
        ;; `backend/x86-64.cljc` and `backend/aarch64.cljc`) require `value`
        ;; to be a directly-nested, same-schema `record-new` -- this
        ;; independent re-check enforces the EXACT same narrow shape (rather
        ;; than relying solely on `verify-runtime!`'s `(emit program)`
        ;; re-invocation to fail closed on anything looser), matching this
        ;; file's own "treat embedded KIR as hostile" posture for every
        ;; other op-family above.
        (= op 'record-get)
        (let [[type value field] args]
          (when-not (and (= 3 (count args))
                        (native-scalar-record-type? type)
                        (keyword? field)
                        (some #(= field (first %)) (nth type 2))
                        (= type (record-schema-of value locals)))
            (reject! "runtime KIR record projection rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts))

        ;; ADR 0063, mirroring `record-new` immediately above: the tag must
        ;; be one of the type's own declared cases.
        (= op 'variant-new)
        (let [[type tag payload] args
              case-type (when (native-scalar-variant-type? type)
                          (some (fn [[case-tag payload-type]]
                                  (when (= case-tag tag) payload-type))
                                (nth type 2)))]
          (when-not (and (= 3 (count args)) case-type)
            (reject! "runtime KIR variant construction rejected" {:operation op}))
          (verify-expr! payload locals signatures (inc depth) nodes facts))

        ;; ADR 0063, mirroring `record-get` immediately above: the codegen
        ;; backends (`emit-variant-match-of-new` in both `backend/x86-
        ;; 64.cljc` and `backend/aarch64.cljc`) require `value` to be a
        ;; directly-nested, same-schema `variant-new` -- this independent
        ;; re-check enforces the EXACT same narrow shape. `branches` must
        ;; exhaustively cover every declared case, in the SAME order (the
        ;; ordinal each branch corresponds to is its position).
        (= op 'variant-match)
        (let [[type value branches] args
              cases (when (native-scalar-variant-type? type) (nth type 2))]
          (when-not (and (= 3 (count args)) cases
                        (vector? branches) (= (mapv first cases) (mapv first branches))
                        (every? #(and (vector? %) (= 3 (count %)) (valid-name? (second %))) branches)
                        (seq? value) (= 'variant-new (first value)) (= type (second value))
                        (some #(= (nth value 2) (first %)) cases))
            (reject! "runtime KIR variant dispatch rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts)
          ;; Each branch's binder carries the schema of ITS OWN declared case
          ;; payload when that payload is a record, so a projection inside the
          ;; branch is checkable the same way one over a let-bound record is.
          ;; Cases and branches are already known to be tag-aligned above.
          (doseq [[[_ payload-type] [_ binder body]] (map vector cases branches)]
            (verify-expr! body
                          (assoc locals binder
                                 (when (native-scalar-record-type? payload-type) payload-type))
                          signatures (inc depth) nodes facts)))

        (contains? '#{option-some-of option-some?-of} op)
        (let [[type value] args]
          (when-not (and (= 2 (count args))
                         (vector? type) (= :option (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR generic option operation rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts))

        (= op 'option-none-of)
        (let [[type] args]
          (when-not (and (= 1 (count args))
                         (vector? type) (= :option (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR generic option operation rejected" {:operation op})))

        (= op 'option-value-of)
        (let [[type value fallback] args]
          (when-not (and (= 3 (count args))
                         (vector? type) (= :option (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR generic option projection rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts)
          (verify-expr! fallback locals signatures (inc depth) nodes facts))

        (= op 'option-match)
        (let [[type value none-body binder some-body] args]
          (when-not (and (= 5 (count args))
                         (vector? type) (= :option (first type))
                         (native-word-value-type? type)
                         (valid-name? binder))
            (reject! "runtime KIR generic option match rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts)
          (verify-expr! none-body locals signatures (inc depth) nodes facts)
          (verify-expr! some-body (assoc locals binder nil) signatures
                        (inc depth) nodes facts))

        (contains? '#{result-ok-of result-err-of result-ok?-of} op)
        (let [[type value] args]
          (when-not (and (= 2 (count args))
                         (vector? type) (= :result (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR generic result operation rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts))

        (contains? '#{result-value-of result-error-of} op)
        (let [[type value fallback] args]
          (when-not (and (= 3 (count args))
                         (vector? type) (= :result (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR generic result projection rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts)
          (verify-expr! fallback locals signatures (inc depth) nodes facts))

        (= op 'result-match-of)
        (let [[type value ok-binder ok-body err-binder err-body] args]
          (when-not (and (= 6 (count args))
                         (vector? type) (= :result (first type))
                         (native-word-value-type? type)
                         (valid-name? ok-binder) (valid-name? err-binder))
            (reject! "runtime KIR generic result match rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts)
          (verify-expr! ok-body (assoc locals ok-binder nil) signatures
                        (inc depth) nodes facts)
          (verify-expr! err-body (assoc locals err-binder nil) signatures
                        (inc depth) nodes facts))

        (contains? heap-operations op)
        (do
          (when-not (= (get heap-operations op) (count args))
            (reject! "runtime KIR heap operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? kgraph-operations op)
        (do
          (when-not (= (get kgraph-operations op) (count args))
            (reject! "runtime KIR kgraph operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? string-operations op)
        (do
          (when-not (= (get string-operations op) (count args))
            (reject! "runtime KIR string operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? tagged-i64-operations op)
        (do
          (when-not (= (get tagged-i64-operations op) (count args))
            (reject! "runtime KIR tagged i64 operation arity rejected"
                     {:operation op}))
          (doseq [arg args]
            (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? xml-operations op)
        (do
          (when-not (= (get xml-operations op) (count args))
            (reject! "runtime KIR XML operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? decimal-operations op)
        (do
          (when-not (= (get decimal-operations op) (count args))
            (reject! "runtime KIR decimal operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? '#{kernel-load-u8 kernel-load-u8-4k kernel-load-u8-16k
                      kernel-store-u8 kernel-store-u8-4k kernel-subregion
                      kernel-load-u32 kernel-store-u32} op)
        (do
          (when-not (= ({'kernel-load-u8 3 'kernel-load-u8-4k 3
                         'kernel-load-u8-16k 3 'kernel-store-u8 4
                         'kernel-store-u8-4k 4 'kernel-subregion 4
                         'kernel-load-u32 3 'kernel-store-u32 4} op) (count args))
            (reject! "runtime KIR kernel memory operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? '#{kernel-boot-info kernel-read-cr2 kernel-read-cr3 kernel-write-cr3 kernel-invlpg
                      kernel-cli kernel-sti kernel-hlt kernel-pause
                      kernel-out-u8 kernel-out-u32} op)
        (do
          (when-not (= ({'kernel-boot-info 0 'kernel-read-cr2 0 'kernel-read-cr3 0 'kernel-write-cr3 1
                         'kernel-invlpg 1 'kernel-cli 0 'kernel-sti 0 'kernel-hlt 0
                         'kernel-pause 0 'kernel-out-u8 2 'kernel-out-u32 2} op)
                       (count args))
            (reject! "runtime KIR kernel privileged operation arity rejected"
                     {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        ;; f64 scalar arithmetic. Each takes and returns one machine word --
        ;; an IEEE-754 bit pattern -- allocates nothing and touches no memory,
        ;; so verification is an arity check plus a walk of the operands,
        ;; exactly as for the integer arithmetic above.
        (contains? '#{f64-add f64-sub f64-mul f64-div f64-min f64-max
                      f64-abs f64-neg f64-sqrt f64-from-bits f64-to-bits
                      f64-eq f64-lt f64-le f64-gt f64-ge f64-unordered} op)
        (do
          (when-not (= ({'f64-add 2 'f64-sub 2 'f64-mul 2 'f64-div 2
                         'f64-min 2 'f64-max 2
                         'f64-abs 1 'f64-neg 1 'f64-sqrt 1
                         'f64-from-bits 1 'f64-to-bits 1
                         'f64-eq 2 'f64-lt 2 'f64-le 2 'f64-gt 2 'f64-ge 2
                         'f64-unordered 2} op)
                       (count args))
            (reject! "runtime KIR f64 operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? signatures op)
        (do
          (when-not (= (count (get signatures op)) (count args))
            (reject! "runtime KIR call arity rejected" {:function op}))
          (vswap! facts update :calls conj op)
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        :else (reject! "runtime KIR operation rejected" {:operation op})))

    :else (reject! "runtime KIR value type rejected" {:value form})))

(defn- infer-effects [direct]
  (loop [inferred (into {} (map (fn [[name facts]] [name (:effects facts)]) direct))]
    (let [next-effects
          (into {} (map (fn [[name {:keys [effects calls]}]]
                          [name (reduce set/union effects (map #(get inferred % #{}) calls))])
                        direct))]
      (if (= inferred next-effects) inferred (recur next-effects)))))

;; `:i64` only -- but as a CONSEQUENCE of unfinished work, not as a judgement
;; that `:bool` is wrong here. Widening this set alone would not help, and the
;; reason is worth stating precisely, because the obvious reading of the native
;; backends gets it backwards.
;;
;; The convention is already decided (`kotoba-kir` 38d1bd0, 2026-07-31, "box a
;; :bool result at the execute boundary"): `:bool` is a plain 0/1 word INSIDE
;; the interpreter, inside a wasm module, and in the native backends' own
;; setcc/cset sequences -- but the value that LEAVES a target is a host
;; boolean. `kotoba.wasm.core` emits an export wrapper that boxes one, the
;; restricted-ESM emitter returns one, and the reference interpreter was made
;; to box one so all three shared corpora agree on the same value for a
;; predicate. A `:bool` ARGUMENT has always required a real boolean, so the two
;; directions are symmetric.
;;
;; Native is simply the target that has not been carried across that boundary
;; yet. Measured 2026-08-03 for `(defn main [] (= 1 1))`:
;;
;;   kotoba.kir/lower     :oracle-value  nil     -- its fold guard is :i64-only
;;   kotoba.kir/execute                  true    -- boxed, per 38d1bd0
;;
;; versus `(+ 1 1)`, where both are `2`. So the oracle cannot be sealed for a
;; `:bool` entry at all, and this set is downstream of that.
;;
;; The visible consequence: because comparisons infer `:bool`,
;; `(defn main [] (< a b))` compiles for wasm32, js and cljs but NOT for
;; native, and a predicate can only appear in an `if` test position there.
;;
;; That is now done. `kotoba.kir/lower` folds a `:bool` entry and seals the
;; BOXED boolean (its `:blocks` keep the 0/1 word, which 38d1bd0 explicitly
;; leaves as the internal representation), so `verify-native-artifact!`'s own
;; re-execution through `execute` -- which boxes the same way -- is directly
;; comparable to it. `kototama.native.executor` boxes at its report boundary
;; for the same reason.
;;
;; Note that this set is only reachable at all because `lower` now seals
;; something: widening it on its own would have changed nothing.
(def ^:private entry-result-types #{:i64 :bool})

;; An INTERNAL function may also return a `:string`. This is deliberately wider
;; than `entry-result-types`, and the two are separate because they answer
;; different questions: the entry's result crosses to the host, which is why
;; `:bool` needed boxing on every target before it could be admitted there,
;; whereas an internal result only has to be a value the ABI can carry in a
;; register.
;;
;; A string already is such a value -- it IS a pair(offset,length) handle, one
;; word, indistinguishable from an i64 at a call boundary -- and this same shape
;; check has always admitted `:string` PARAMETERS. Admitting it in one direction
;; and not the other was an asymmetry rather than a rule: it made
;; `(defn f [n] (string-substring ...))` unverifiable, and with it every
;; string-returning helper the frontend synthesizes, `string-from-i64` among
;; them. Nothing had a string-returning function before, so nothing caught it.
(def ^:private function-result-types #{:i64 :bool :string})

;; Each shape condition is named so a rejection can say which one failed. The
;; whole set used to be one `and` reporting `{}`, which meant the most common
;; way to hit it -- an entry returning `:bool` -- surfaced as "module shape
;; rejected" with nothing to go on. A verifier may refuse anything it likes,
;; but it must be possible to learn what it refused.
(def ^:private module-shape-checks
  [[:map (fn [p] (map? p))]
   [:keys (fn [p] (= #{:format :entry :exports :signature :effects :functions} (set (keys p))))]
   [:format (fn [p] (contains? #{:kotoba.kir/v3 :kotoba.kir/v4} (:format p)))]
   [:entry (fn [p] (= 'main (:entry p)))]
   [:signature-params (fn [p] (= [] (:params (:signature p))))]
   [:signature-result (fn [p] (contains? entry-result-types (:result (:signature p))))]
   [:signature-keys (fn [p] (= #{:params :result} (set (keys (:signature p)))))]
   [:effects-set (fn [p] (set? (:effects p)))]
   [:effects-valid (fn [p] (every? valid-effect? (:effects p)))]
   [:functions-vector (fn [p] (vector? (:functions p)))]
   [:exports-vector (fn [p] (vector? (:exports p)))]
   [:function-count (fn [p] (<= 1 (count (:functions p)) max-functions))]])

(defn- valid-closure-param-indexes? [function]
  (if-not (contains? function :closure-param-indexes)
    true
    (let [indexes (:closure-param-indexes function)
          param-types (or (:param-types function)
                          (vec (repeat (count (:params function)) :i64)))]
      (and (vector? indexes)
           (= indexes (vec (sort (distinct indexes))))
           (every? #(and (integer? %) (<= 0 %)
                         (< % (count (:params function)))
                         (= :i64 (nth param-types % nil)))
                   indexes)))))

(defn- valid-i64-pair-chain-param-indexes? [function]
  (if-not (contains? function :i64-pair-chain-param-indexes)
    true
    (let [indexes (:i64-pair-chain-param-indexes function)
          closure-indexes (set (:closure-param-indexes function))
          param-types (or (:param-types function)
                          (vec (repeat (count (:params function)) :i64)))]
      (and (vector? indexes)
           (= indexes (vec (sort (distinct indexes))))
           (not-any? closure-indexes indexes)
           (every? #(and (integer? %) (<= 0 %)
                         (< % (count (:params function)))
                         (= :i64 (nth param-types % nil)))
                   indexes)))))

(defn- valid-closure-result-refinement? [function]
  (if-not (contains? function :closure-result?)
    true
    (and (true? (:closure-result? function))
         (= :i64 (:result function)))))

(defn- verify-program! [program]
  (doseq [[label check] module-shape-checks]
    ;; A hostile program can fail an early check in a way that makes a later
    ;; one throw rather than return false, so each is guarded and a throw is
    ;; treated as a failure of that same named condition.
    (when-not (try (boolean (check program)) (catch #?(:clj Throwable :cljs :default) _ false))
      (reject! "runtime KIR module shape rejected" {:condition label})))
  (binding [*call-results* (into {} (map (juxt :name :result) (:functions program)))]
   (let [functions (:functions program)
        signatures
        (into {}
              (map (fn [function]
                     (when-not (and (map? function)
                                    (let [keys* (set (keys function))
                                          required #{:name :params :result :effects :body}
                                          admitted (conj required :param-types
                                                         :closure-param-indexes
                                                         :i64-pair-chain-param-indexes
                                                         :closure-result?)]
                                      (and (set/subset? required keys*)
                                           (set/subset? keys* admitted)))
                                    (valid-name? (:name function))
                                    (vector? (:params function))
                                    (<= (count (:params function)) max-parameters)
                                    (every? valid-name? (:params function))
                                    (= (count (:params function))
                                       (count (distinct (:params function))))
                                    ;; A function may also return a RECORD, which
                                    ;; crosses the boundary boxed as a pair
                                    ;; chain -- one word, built from the arena
                                    ;; primitives already contracted here.
                                    (or (contains? function-result-types (:result function))
                                        (native-scalar-record-type? (:result function)))
                                    (or (not (contains? function :param-types))
                                        (and (vector? (:param-types function))
                                             (= (count (:param-types function)) (count (:params function)))
                                             (every? #{:i64 :string} (:param-types function))))
                                    (valid-closure-param-indexes? function)
                                    (valid-i64-pair-chain-param-indexes? function)
                                    (valid-closure-result-refinement? function)
                                    (set? (:effects function))
                                    (every? valid-effect? (:effects function)))
                       (reject! "runtime KIR function shape rejected" {:function (:name function)}))
                     [(:name function) (:params function)]))
              functions)]
    (when-not (and (= (count functions) (count signatures)) (contains? signatures 'main)
                   (empty? (get signatures 'main))
                   (= (count (:exports program)) (count (distinct (:exports program))))
                   (every? #(contains? signatures %) (:exports program))
                   (some #{'main} (:exports program)))
      (reject! "runtime KIR entry or function identity rejected" {}))
    (let [nodes (volatile! 0)
          direct
          (into {}
                (map (fn [function]
                       (let [facts (volatile! {:effects #{} :calls #{}})]
                         (verify-expr! (:body function) (zipmap (:params function) (repeat nil))
                                       signatures 0 nodes facts)
                         [(:name function) @facts])))
                functions)
          inferred (infer-effects direct)
          declared (into {} (map (juxt :name :effects) functions))
          total (reduce set/union #{} (vals inferred))
          cost (bounded-sum (map #(lowered-cost (:body %) {}) functions))]
      (when-not (= inferred declared)
        (reject! "runtime KIR function effects rejected" {}))
      (when-not (= total (:effects program))
        (reject! "runtime KIR module effects rejected" {}))
      (when (> cost max-lowered-nodes)
        (reject! "runtime KIR lowering budget exhausted" {:cost cost}))))
  program))

(defn- verify-runtime! [{:keys [target program code exports lowering limits fuel-abi context-abi]
                         profile-value :target-profile}]
  (let [backend (target-profile/backend target)
        expected-profile (target-profile/profile target)
        {expected-lowering :lowering emit :emit} (get target-contracts backend)]
    (when (and (not (contains? #{:x86_64-aiueos-kernel-v1 :aarch64-aiueos-kernel-v1} target))
               (some #(and (seq? %) (contains? '#{kernel-load-u8 kernel-load-u8-4k
                                                  kernel-load-u8-16k kernel-store-u8
                                                  kernel-store-u8-4k kernel-load-u32 kernel-store-u32
                                                  kernel-boot-info kernel-read-cr2
                                                  kernel-read-cr3 kernel-write-cr3 kernel-invlpg
                                                  kernel-cli kernel-sti kernel-hlt kernel-pause
                                                  kernel-out-u8 kernel-out-u32} (first %)))
                     (tree-seq coll? seq (:functions program))))
      (reject! "bounded kernel memory operation requires the aiueos kernel target"
               {:target target}))
    (when-not (= expected-profile profile-value)
      (reject! "native target profile does not match target identity" {:target target}))
    (when-not emit (reject! "not a native verifier target" {:target target}))
    (when-not (= expected-lowering lowering)
      (reject! "native runtime lowering mode is not admitted"
               {:target target :lowering lowering}))
    (when-not (contains? #{:kotoba.kir/v3 :kotoba.kir/v4} (:format program))
      (reject! "native artifact requires runtime KIR v3 or v4"
               {:target target :program-format (:format program)}))
    (verify-program! program)
    (let [expected (try (emit program)
                        (catch #?(:clj Exception :cljs :default) e
                          (reject! "runtime KIR cannot be safely lowered"
                                   {:target target :cause (ex-message e)})))]
      (when-not (= (:exports expected) exports)
        (reject! "native export table rejected" {:target target}))
      (when-not (= (:code expected) code)
        (reject! "native instruction stream rejected" {:target target})))
    (let [expected-fuel-abi (case backend
                              :x86_64-kotoba-v1 {:mode :hidden-context-r9 :initial 512}
                              :aarch64-kotoba-v1 {:mode :hidden-context-x7 :initial 512})
          expected-limits {:memory-bytes 65536
                           :fuel 512
                           :stack-bytes 4096}
          expected-context {:version 2 :fuel-offset 8 :allow-bitmap-offset 16
                            :allow-bitmap-bytes 32 :cap-call-offset 48
                            :pair-new-offset 56 :pair-first-offset 64
                            :pair-second-offset 72 :pair-capacity 4096
                            :kgraph-assert-offset 80 :kgraph-get-offset 88
                            :kgraph-count-offset 96 :kgraph-entity-at-offset 104
                            :kgraph-capacity 4096
                            :string-equal-offset 112 :string-concat-offset 120
                            :typed-cap-call-offset 128
                            :string-substring-offset 136
                            :string-code-point-at-offset 144
                            :string-pool-capacity 65536}]
      (when-not (= expected-fuel-abi fuel-abi)
        (reject! "fuel ABI is not admitted" {:target target :fuel-abi fuel-abi}))
      (when-not (= expected-limits limits)
        (reject! "resource limits are not admitted" {:target target :limits limits}))
      (when-not (= expected-context context-abi)
        (reject! "execution context ABI is not admitted"
                 {:target target :context-abi context-abi})))))

(defn verify-artifact! [{:keys [format target target-profile code effects kir-sha256 compatibility] :as kexe}]
  (when-not (and (map? kexe) (= artifact-fields (set (keys kexe))))
    (reject! "native artifact schema rejected" {}))
  (when-not (= :kotoba.kexe/v1 format) (reject! "unknown artifact format" {}))
  (when-not (and (string? kir-sha256) (re-matches #"[0-9a-f]{64}" kir-sha256))
    (reject! "missing or malformed KIR identity" {}))
  (when-not (= effects (get-in kexe [:program :effects]))
    (reject! "artifact effects do not match runtime KIR" {}))
  (when-not (every? #(and (vector? %) (= :cap/call (first %))
                          (= 2 (count %))
                          #?(:clj (integer? (second %))
                             :cljs (or (i64/bigint-value? (second %)) (integer? (second %))))
                          (<= 0 (second %) 255)) effects)
    (reject! "native artifact contains an unsupported effect" {:effects effects}))
  (when-not (and (vector? code) (<= 1 (count code) (* 1024 1024))
                 (every? #(and (integer? %) (<= 0 % 255)) code))
    (reject! "malformed code bytes" {}))
  (when-not (artifact/valid-seal? kexe) (reject! "artifact integrity mismatch" {}))
  (when-not (= kir-sha256 (artifact/sha256 (:program kexe)))
    (reject! "runtime KIR identity mismatch" {}))
  (verify-runtime! kexe)
  (let [kir-format (get-in kexe [:program :format])
        typed-values? (= :kotoba.kir/v4 kir-format)
        expected (compatibility-profile/descriptor
                  {:hir-format (if typed-values? :kotoba.hir/v3 :kotoba.hir/v2)
                   :kir-format kir-format
                   :target target :target-profile target-profile
                   ;; The compiler picks the value ABI by whether the program
                   ;; uses floating point, before falling back to the typed or
                   ;; direct word ABI. This mirrored only the last two, so an
                   ;; f64 program -- which the compiler stamps
                   ;; :kotoba.typed/mixed-f64-v2 -- could never match anything
                   ;; derivable here. Deriving it from the KIR this verifier
                   ;; holds keeps the check independent of what the artifact
                   ;; claims.
                   :value-abi (cond
                                (ir/uses-f32? (:program kexe)) :kotoba.typed/mixed-f32-f64-v3
                                (ir/uses-f64? (:program kexe)) :kotoba.typed/mixed-f64-v2
                                typed-values? :kotoba.typed/externref-v1
                                :else :kotoba.i64/direct-v1)})]
    (when-not (= expected compatibility)
      (reject! "native compatibility metadata rejected" {:target target})))
  (let [kernel-operations '#{kernel-load-u8 kernel-load-u8-4k kernel-load-u8-16k
                             kernel-store-u8 kernel-store-u8-4k kernel-read-cr2
                             kernel-load-u32 kernel-store-u32
                             kernel-boot-info kernel-read-cr3 kernel-write-cr3 kernel-invlpg
                             kernel-cli kernel-sti kernel-hlt kernel-pause
                             kernel-out-u8 kernel-out-u32}
        kernel-native? (some #(and (seq? %) (contains? kernel-operations (first %)))
                             (tree-seq coll? seq (get-in kexe [:program :functions])))
        expected-value
        (when (and (empty? effects) (not kernel-native?))
          (try
            (ir/execute (:program kexe) (get-in kexe [:program :entry]) [])
            (catch #?(:clj Exception :cljs :default) error
              (reject! "native artifact oracle evaluation rejected"
                       {:cause (ex-message error)}))))]
    (when-not (= expected-value (:value kexe))
      (reject! "native artifact oracle value rejected" {})))
  kexe)
