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

(def ^:private max-native-fuel 1048576)

(defn- admitted-native-fuel? [fuel]
  (and #?(:clj (integer? fuel)
          :cljs (or (i64/bigint-value? fuel) (integer? fuel)))
       (<= 1 fuel max-native-fuel)))

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
;;
;; `string-contains?` and `string-replace-all` are admitted on the same stance,
;; and the stance is the whole reason they belong here rather than in a
;; native-only table. They are target-independent operations: `kotoba-wasm`
;; has been the semantic oracle for both since long before either had a native
;; lowering, and `kotoba.kir/execute` runs them. What was missing was only a
;; native EMISSION, and that landed in kotoba-native `5df4d85`
;; (`kotoba.native.string-search`, its ADR 0002) as a source rewrite into the
;; four string callbacks already listed above -- `string=?`, `string-concat`,
;; `string-substring`, `string-code-point-at` -- so this verifier is not
;; ratifying a new capability, only ceasing to refuse an operation whose
;; contract it always had.
;;
;; The arities are the KIR arities, independently re-derived like every other
;; entry in this file, and they are the shapes both backends dispatch on
;; (`x86_64.cljc` 1189/1192, `aarch64.cljc` 988/991). A different arity has no
;; lowering and is refused by the arity check this table drives.
;;
;; Measured 2026-08-05: this table is the SECOND of two gates that refused
;; these operations before emission. `kotoba.kir/non-string-typed-ops` is the
;; first, and opening either one alone unlocks nothing -- the lowering moved
;; murakumo's shipped-core sweep by exactly zero until both landed. See ADR
;; 0002 here, and `kotoba-kir` ADR 0222 for the other gate.
(def ^:private string-operations
  '{string-byte-length 1 string=? 2 string-concat 2 string-substring 3 string-code-point-at 2
    string-contains? 2 string-replace-all 3
    keyword-name 1 keyword-from-string 1})
(def ^:private tagged-i64-operations
  '{option-some 1 option-none 0 option-some? 1 option-value 2
    result-ok 1 result-err 1 result-ok? 1 result-value 2 result-error 2})

(def ^:private native-clock-request-type
  [:variant :kotoba.clock/request [[:wall :bool] [:monotonic :bool]]])

(def ^:private native-clock-result-type
  [:variant :kotoba.clock/result
   [[:wall [:record :kotoba.clock/wall
            [[:unix-millis :i64] [:observation-sequence :i64]]]]
    [:monotonic [:record :kotoba.clock/monotonic
                 [[:nanos :i64] [:observation-sequence :i64]]]]
    [:error [:record :kotoba.clock/error
             [[:code :keyword] [:message :string]]]]]])

(def ^:private native-dataspace-request-type
  [:variant :kotoba.dataspace/request
   [[:assert [:record :kotoba.dataspace/assert
              [[:assertion :document] [:facet :i64]]]]
    [:retract [:record :kotoba.dataspace/retract
               [[:assertion :document] [:facet :i64]]]]
    [:observe [:record :kotoba.dataspace/observe
               [[:pattern :document] [:facet :i64]]]]
    [:facet-enter :bool]
    [:facet-leave :i64]]])

(def ^:private native-dataspace-result-type
  [:variant :kotoba.dataspace/result
   [[:asserted [:record :kotoba.dataspace/asserted
                [[:count :i64] [:notices :document]]]]
    [:retracted [:record :kotoba.dataspace/retracted [[:count :i64]]]]
    [:matches [:record :kotoba.dataspace/matches
               [[:bindings :document] [:notices :document]]]]
    [:facet [:record :kotoba.dataspace/facet [[:id :i64]]]]
    [:error [:record :kotoba.dataspace/error
             [[:code :keyword] [:message :string]]]]]])

(def ^:private native-ui-parent-type [:option :keyword])
(def ^:private native-ui-node-type
  [:record :kotoba.ui/node
   [[:id :keyword] [:parent native-ui-parent-type]
    [:kind :keyword] [:text :string]]])
(def ^:private native-ui-node-set-type [:set native-ui-node-type])
(def ^:private native-ui-commit-request-type
  [:record :kotoba.ui/commit-request
   [[:base-revision :i64] [:nodes native-ui-node-set-type]]])
(def ^:private native-ui-commit-result-type
  [:record :kotoba.ui/commit-result [[:revision :i64] [:node-count :i64]]])
(def ^:private native-ui-event-request-type
  [:record :kotoba.ui/event-request [[:after-revision :i64]]])
(def ^:private native-ui-event-type
  [:record :kotoba.ui/event
   [[:revision :i64] [:target :keyword] [:kind :keyword] [:value :string]]])
(def ^:private native-ui-event-result-type [:option native-ui-event-type])

(defn- native-provider-contract? [cap-id request-type result-type]
  (or (and (= 7 cap-id)
           (= native-clock-request-type request-type)
           (= native-clock-result-type result-type))
      (and (= 24 cap-id)
           (= native-dataspace-request-type request-type)
           (= native-dataspace-result-type result-type))
      (and (= 9 cap-id)
           (= native-ui-commit-request-type request-type)
           (= native-ui-commit-result-type result-type))
      (and (= 10 cap-id)
           (= native-ui-event-request-type request-type)
           (= native-ui-event-result-type result-type))))
;; `vector-i64` / `vector-f64` (ADR-2608030300). Admitted here as the
;; target-independent operations they are, with their KIR arities -- the same
;; stance `string-operations` above takes, and for the same reason: a backend
;; that cannot emit one of these reports it as not implemented, which is
;; accurate and fail-closed, whereas encoding a backend's limits here would
;; make this verifier ratify one target's reach as if it were the contract.
;;
;; The two families are listed separately rather than folded together even
;; though the native backends lower them to the same host calls. This
;; verifier re-checks KIR, and in KIR they ARE two families with two element
;; validations; collapsing them here would be re-deriving the emitter's
;; simplification instead of the contract.
(def ^:private vector-operations
  '{vector-count 1 vector-get 3 vector-at 2 vector-drop 2
    vector-assoc 3 vector-conj 2
    vector-f64-count 1 vector-f64-get 3 vector-f64-at 2 vector-f64-drop 2
    vector-f64-assoc 3 vector-f64-conj 2
    ;; `vector-alloc` allocates n zeros; `vector-assoc!` is `vector-assoc`
    ;; with the caller's claim that the handle is dead afterwards, which lets
    ;; a backend lower the update to a store. Both re-derived here rather than
    ;; imported, like every other entry in this file: producer and verifier
    ;; move in the same closure and neither trusts the other's tables.
    ;;
    ;; The bang has the SAME arity as the operation without it, and must: KIR
    ;; evaluates them identically, so a different shape here would make the
    ;; bang a different operation. Neither has an f64 twin, because KIR
    ;; declares none.
    vector-alloc 1 vector-assoc! 3})
;; `vector-new` is the one variadic operation in either family: its arity IS
;; the literal's element count. Independently re-derived from
;; `kotoba.kir.value/vector-item-limit`, like every other bound in this file.
(def ^:private vector-constructors '#{vector-new vector-f64-new})
(def ^:private max-vector-literal-items 16384)
(def ^:private string-index-operations
  '{string-index-new 0 string-index-count 1 string-index-contains 2
    string-index-get 2 string-index-assoc 3})
(def ^:private max-string-index-items 128)
(def ^:private max-string-index-key-bytes 65536)
(def ^:private xml-operations
  '{xml-path-count 2 xml-name-count 2 xml-name-text 3 xml-path-text 3 xml-path-attr 4})
(def ^:private decimal-operations '{decimal-f64-parse 1 decimal-f64x3-parse 1})
(def ^:private string-literal-byte-limit 4096)
(def ^:private max-record-fields 32)
(def ^:private max-record-nesting-depth 32)

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
(def ^:private native-word-field-types #{:i64 :bool :string :keyword :document})

(declare native-scalar-record-type?)
(declare native-word-value-type?)

(defn- native-scalar-record-type?
  ([type] (native-scalar-record-type? type 0))
  ([type depth]
   (and (< depth max-record-nesting-depth)
        (vector? type) (= 3 (count type)) (= :record (first type))
        (keyword? (second type)) (some? (namespace (second type)))
        (vector? (nth type 2)) (seq (nth type 2))
        (<= (count (nth type 2)) max-record-fields)
        (every? (fn [field]
                  (and (vector? field) (= 2 (count field)) (keyword? (first field))
                       ;; ABI v6 represents a nested record as one pair-chain
                       ;; handle. Re-derive the producer's depth bound here;
                       ;; importing its predicate would defeat verification.
                       (or (contains? native-word-field-types (second field))
                           ;; An `[:option T]`/`[:result T E]` field already
                           ;; travels as ONE word (the pair handle).
                           (native-word-value-type? (second field))
                           (native-scalar-record-type? (second field) (inc depth)))))
                (nth type 2))
        (= (count (nth type 2))
           (count (distinct (map first (nth type 2))))))))

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

(defn- native-scalar-variant-boundary-type?
  "Independent copy of aggregate ABI v7's one-word public boundary."
  [type]
  (and (vector? type) (= 3 (count type)) (= :variant (first type))
       (keyword? (second type)) (some? (namespace (second type)))
       (vector? (nth type 2)) (<= 1 (count (nth type 2)) max-variant-cases)
       (every? #(and (vector? %) (= 2 (count %))
                     (keyword? (first %))
                     (or (contains? #{:i64 :bool} (second %))
                         (native-scalar-record-type? (second %))))
               (nth type 2))
       (= (count (nth type 2))
          (count (distinct (map first (nth type 2)))))))

(defn- native-word-value-type?
  "Independent verifier copy of the recursive one-word native value slice."
  ([type] (native-word-value-type? type 0))
  ([type depth]
   (and (<= depth 8)
        (or (contains? #{:i64 :bool :string :keyword :document
                         :option-i64 :result-i64} type)
            (and (vector? type)
                 (case (first type)
                   :option (and (= 2 (count type))
                                (or (native-word-value-type? (second type) (inc depth))
                                    (native-scalar-record-type? (second type))))
                   :set (and (= 2 (count type))
                             (or (native-word-value-type? (second type) (inc depth))
                                 (native-scalar-record-type? (second type))))
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
    (and (seq? form) (= 'typed-set-new (first form)))
    (let [[_ _type & items] form]
      (bounded-sum (cons 1 (map #(lowered-cost % env) items))))
    (and (seq? form) (= 'typed-set-conj (first form)))
    (let [[_ _type value item] form]
      (bounded-sum [1 (lowered-cost value env) (lowered-cost item env)]))
    (and (seq? form) (contains? '#{typed-set-count typed-set-nth} (first form)))
    (let [[_ _type & rest] form]
      (bounded-sum (cons 1 (map #(lowered-cost % env) rest))))
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

;; The exact aggregate family kotoba-native may keep as an ordered SSA bundle.
;; This is deliberately narrower than `native-scalar-record-type?`, which also
;; describes legacy one-word/flattened representations. SROA currently owns no
;; string, option/result, or nested-record representation.
(defn- scalar-replaced-record-type? [type]
  (and (native-scalar-record-type? type)
       (every? #(contains? #{:i64 :bool} (second %)) (nth type 2))))

;; The exact sealed-variant family kotoba-native may keep as a tag/payload SSA
;; bundle. The legacy emitter admits additional one-word and record payloads;
;; those remain available only to its directly nested match shape.
(defn- scalar-replaced-variant-type? [type]
  (and (native-scalar-variant-type? type)
       (every? #(contains? #{:i64 :bool} (second %)) (nth type 2))))

(defn- boxed-aggregate-variant-type? [type]
  (and (native-scalar-variant-boundary-type? type)
       (boolean (some #(native-scalar-record-type? (second %))
                      (nth type 2)))))

;; A value-position IF may transport an SROA bundle only when both branches
;; construct the same exact record type. Conditions stay scalar and are checked
;; separately by `verify-expr!`. Do not resolve symbols here: forwarding a
;; flattened record through a second binding remains outside the emitter.
(defn- record-sroa-if-schema [value]
  (when (and (seq? value) (= 'if (first value)) (= 4 (count value)))
    (let [[_ _test then-value else-value] value
          then-schema (record-new-schema then-value)
          else-schema (record-new-schema else-value)]
      (when (and (= then-schema else-schema)
                 (scalar-replaced-record-type? then-schema))
        then-schema))))

(defn- variant-new-schema [value]
  (when (and (seq? value) (= 'variant-new (first value)) (= 4 (count value)))
    (let [[_ type tag _payload] value]
      (when (and (or (scalar-replaced-variant-type? type)
                     (boxed-aggregate-variant-type? type))
                 (some #(= tag (first %)) (nth type 2)))
        type))))

;; Like records, the only value-position IF remembered as a local variant is
;; one whose two arms directly construct the identical scalar-replaced schema.
;; Symbols are deliberately not resolved here, preventing aggregate forwarding.
(defn- variant-sroa-if-schema [value]
  (when (and (seq? value) (= 'if (first value)) (= 4 (count value)))
    (let [[_ _test then-value else-value] value
          then-schema (variant-new-schema then-value)
          else-schema (variant-new-schema else-value)]
      (when (= then-schema else-schema) then-schema))))

(defn- variant-local [type]
  {:aggregate/kind :variant :aggregate/type type})

(declare ^:dynamic *call-results*)

(defn- provider-result-schema
  "Result type of a sealed provider typed-cap-call
  (clock 7, dataspace 24, ui commit 9, ui event 10).

  The host returns a nested pair handle, not a local SROA construction.
  Matching that boundary is how a guest reads unix-millis, notices, or a
  UI revision; it is not a widening of local SROA."
  [form]
  (when (and (seq? form) (= 'typed-cap-call (first form)) (= 5 (count form))
             (native-provider-contract? (nth form 1) (nth form 2) (nth form 3)))
    (nth form 3)))

(defn- variant-schema-of [form locals]
  (cond
    ;; Preserve ADR 0063's broader legacy direct-match family.
    (and (seq? form) (= 'variant-new (first form)) (= 4 (count form))
         (native-scalar-variant-type? (second form)))
    (second form)

    (and (seq? form) (= 'if (first form)))
    (variant-sroa-if-schema form)

    (provider-result-schema form)
    (provider-result-schema form)

    (symbol? form)
    (let [local (get locals form)]
      (when (= :variant (:aggregate/kind local)) (:aggregate/type local)))

    (and (seq? form) (simple-symbol? (first form))
         (contains? *call-results* (first form)))
    (let [result (get *call-results* (first form))]
      (when (native-scalar-variant-boundary-type? result) result))

    :else nil))

(declare record-schema-of)

;; Declared result type per function, for resolving a record that arrives boxed
;; across a call boundary. Bound once per program by `verify-program!`.
(def ^:dynamic *call-results* {})

;; `[:ref :ns/name]` -- a schema reference, which is the ONE spelling that
;; survives lowering into a signature. `lower` expands references inside
;; expressions but leaves signatures alone, because expanding one in a signature
;; moved the `:kir-sha256` of every module that used a schema reference, on
;; every target including its Wasm bytes. Re-derived here, exactly as
;; `native-boundary-type?`'s own last clause spells it.
(defn- record-reference? [type]
  (and (vector? type) (= 2 (count type)) (= :ref (first type))
       (keyword? (second type)) (some? (namespace (second type)))))

;; The record schema a CALL denotes, or nil -- read off the callee's declared
;; result.
;;
;; Both spellings are admitted, and the reference is returned AS the reference
;; rather than resolved: the verified `program` carries no schema table to
;; expand it with (`program` is `select-keys`-ed to the exact set `:kir-sha256`
;; digests, and widening that set would move the digest of every module using a
;; schema reference). `record-get`'s own check then requires the projected type
;; to be a well-formed `native-scalar-record-type?` whose NAME equals the
;; reference -- the same by-name discipline a record PARAMETER declared by
;; reference has always been held to. Admitting the name is not taking the
;; record on trust; projecting schema A through a result declared as a
;; reference to B is still rejected.
;;
;; Before this, only `native-scalar-record-type?` was accepted, so a call
;; declared `[:ref :t/r]` resolved to nil and every projection over it was
;; refused -- while the identical program with the result written inline was
;; admitted. The backends never distinguished the two spellings (kotoba-native
;; pins that with `a-result-declared-by-schema-reference-boxes-identically`);
;; only this resolver did.
(defn- call-record-schema [form]
  (when (and (seq? form) (simple-symbol? (first form))
             (contains? *call-results* (first form)))
    (let [r (get *call-results* (first form))]
      (when (or (native-scalar-record-type? r) (record-reference? r)) r))))

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
    ;; The same exact SROA IF may be projected directly or named by one let.
    ;; `record-sroa-if-schema` deliberately does not resolve symbols, so this
    ;; does not turn into general aggregate inference or forwarding.
    (and (seq? form) (= 'if (first form))) (record-sroa-if-schema form)
    (symbol? form) (get locals form)
    ;; A call whose declared result is a record: the operand arrived boxed.
    (and (seq? form) (simple-symbol? (first form)) (contains? *call-results* (first form)))
    (call-record-schema form)
    (and (seq? form) (= 'record-get (first form)) (= 4 (count form)))
    (let [[_ type value field] form]
      (when (= type (record-schema-of value locals))
        (let [field-type (second (first (filter #(= field (first %)) (nth type 2))))]
          (when (native-scalar-record-type? field-type) field-type))))
    (and (seq? form) (= 'typed-cap-call (first form)) (= 5 (count form))
         (native-provider-contract? (nth form 1) (nth form 2) (nth form 3))
         (native-scalar-record-type? (nth form 3)))
    (nth form 3)
    :else nil))

;; The record schema a LET BINDING's value denotes, or nil.
;;
;; Three shapes, deliberately. A directly-nested `record-new`, which
;; is FLATTENED into one slot per field by the backends. And a CALL whose
;; declared result is a record, which arrives as the one-word pair-chain handle
;; a record result has crossed on since kotoba-native ADR 0062 --
;; `(let [ends (partition-3-ends x)] (record-get … ends :hi0))`, which is how
;; murakumo's plan and schedule cores read a multi-field result, and the last
;; shape in those cores with no native lowering.
;;
;; The third is one value-position IF whose two branches directly construct the
;; same exact i64/bool record. The native pilot scalar-replaces that shape and
;; emits one phi per field, so the binding carries the same ordered bundle.
;;
;; A sealed UI commit typed-cap-call is the fourth: the host returns a
;; record pair handle (revision + node-count), the same width as a boxed
;; record result. Clock and dataspace stay on the variant path below.
;;
;; NOT the general `record-schema-of`. That also resolves a bare SYMBOL, so
;; using it here would admit `(let [r (record-new …) r2 r] (record-get … r2 :b))`
;; -- and a flattened record forwarded through a second binding is N slots being
;; read as one word, which the backends refuse. Rejecting it here keeps this
;; gate no wider than the emitter it re-derives; the two must agree about the
;; shape, not merely both be "narrow".
(defn- binding-record-schema [value]
  (or (record-new-schema value)
      (call-record-schema value)
      (record-sroa-if-schema value)
      (let [result (provider-result-schema value)]
        (when (native-scalar-record-type? result) result))))

(defn- binding-local [value]
  (or (binding-record-schema value)
      (when-let [type (or (variant-new-schema value)
                          (variant-sroa-if-schema value)
                          (provider-result-schema value))]
        (variant-local type))))

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
        (recur (next pairs) (assoc env name (binding-local value))))
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
                         (or (contains? #{[:i64 :i64] [:string :string]
                                          [:option-i64 :option-i64]
                                          [:result-i64 :result-i64]}
                                        [request-type result-type])
                             (native-provider-contract? cap-id request-type result-type)))
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
        ;; `kotoba.native.x86-64` and `kotoba.native.aarch64`) admit `value` in
        ;; exactly four shapes: a directly-nested same-schema `record-new`, a
        ;; local FLATTENED into one slot per field, a PARAMETER, and -- since
        ;; kotoba-native ADR 0004 -- a one-word boxed HANDLE, whether it came
        ;; straight from a call or was named by a `let` first. This independent
        ;; re-check enforces the same set (rather than relying solely on
        ;; `verify-runtime!`'s `(emit program)` re-invocation to fail closed on
        ;; anything looser), matching this file's own "treat embedded KIR as
        ;; hostile" posture for every other op-family above.
        ;;
        ;; The operand's schema comes from `record-schema-of`; what makes the
        ;; handle cases safe is the identity check below, not the shape --
        ;; whichever route the word arrived by, the projected `type` must be a
        ;; well-formed record that IS the one the operand was declared with.
        (= op 'record-get)
        (let [[type value field] args
              declared (record-schema-of value locals)]
          (when-not (and (= 3 (count args))
                        (native-scalar-record-type? type)
                        (keyword? field)
                        (some #(= field (first %)) (nth type 2))
                        ;; The operand's schema must be the one being projected.
                        ;; A parameter declared as `[:ref :ns/name]` carries only
                        ;; the NAME here (the program has no schema table to
                        ;; expand it with), so the identity is checked on that
                        ;; name -- projecting a different schema through it is
                        ;; still rejected, and `type` itself was already required
                        ;; to be a well-formed record just above.
                        (or (= type declared)
                            (and (vector? declared) (= 2 (count declared))
                                 (= :ref (first declared))
                                 (= (second declared) (second type)))))
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

        ;; ADR 0063's legacy path accepts a directly nested construction. The
        ;; extracted producer additionally accepts one local scalar variant,
        ;; constructed directly or by a same-schema IF. `variant-schema-of`
        ;; independently re-derives those shapes, plus a sealed provider
        ;; typed-cap-call result (clock 7 / dataspace 24 host pair handle,
        ;; not local SROA). Branches still exhaustively cover cases in
        ;; ordinal order.
        (= op 'variant-match)
        (let [[type value branches] args
              cases (when (native-scalar-variant-type? type) (nth type 2))
              declared (variant-schema-of value locals)]
          (when-not (and (= 3 (count args)) cases
                        (vector? branches) (= (mapv first cases) (mapv first branches))
                        (every? #(and (vector? %) (= 3 (count %)) (valid-name? (second %))) branches)
                        (= type declared))
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
          (verify-expr! some-body
                        (assoc locals binder
                               (when (native-scalar-record-type? (second type))
                                 (second type)))
                        signatures
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

        (contains? '#{document-edn-read document-edn-print} op)
        (do
          (when-not (= 1 (count args))
            (reject! "runtime KIR document-edn operation arity rejected"
                     {:operation op}))
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

        (contains? vector-operations op)
        (do
          (when-not (= (get vector-operations op) (count args))
            (reject! "runtime KIR vector operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? vector-constructors op)
        (do
          (when (> (count args) max-vector-literal-items)
            (reject! "runtime KIR vector literal exceeds the item limit"
                     {:operation op :items (count args)
                      :limit max-vector-literal-items}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (= op 'typed-set-new)
        (let [[type & items] args]
          (when-not (and (vector? type) (= :set (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR typed-set constructor rejected" {:operation op}))
          (when (> (count items) max-vector-literal-items)
            (reject! "runtime KIR typed-set literal exceeds the item limit"
                     {:operation op :items (count items)
                      :limit max-vector-literal-items}))
          (doseq [item items]
            (verify-expr! item locals signatures (inc depth) nodes facts)))

        (= op 'typed-set-conj)
        (let [[type value item] args]
          (when-not (and (= 3 (count args))
                         (vector? type) (= :set (first type))
                         (native-word-value-type? type))
            (reject! "runtime KIR typed-set conj rejected" {:operation op}))
          (verify-expr! value locals signatures (inc depth) nodes facts)
          (verify-expr! item locals signatures (inc depth) nodes facts))

        (contains? '#{typed-set-count typed-set-nth} op)
        (let [[type & rest] args]
          (when-not (and (vector? type) (= :set (first type))
                         (native-word-value-type? type)
                         (seq rest))
            (reject! "runtime KIR typed-set operation rejected" {:operation op}))
          (doseq [arg rest]
            (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? string-index-operations op)
        (do
          (when-not (= (get string-index-operations op) (count args))
            (reject! "runtime KIR string-index operation arity rejected"
                     {:operation op}))
          ;; Independently re-derived from the language contract. These
          ;; constants intentionally do not import compiler/emitter code.
          (when-not (and (= 128 max-string-index-items)
                         (= 65536 max-string-index-key-bytes))
            (reject! "runtime KIR string-index limits rejected" {}))
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

        ;; `kernel-try-lock-u32`/`kernel-unlock-u32` (amu#625) are members of
        ;; this family, not a new one: same `base length index` shape, same
        ;; bounds check, same arity 3 as the loads. Leaving them out would not
        ;; have been a policy about atomics -- it would have been an
        ;; inconsistency, since every other member of the family is admitted
        ;; here and the verifier rejects by absence.
        (contains? '#{kernel-load-u8 kernel-load-u8-4k kernel-load-u8-16k
                      kernel-store-u8 kernel-store-u8-4k kernel-subregion
                      kernel-load-u32 kernel-store-u32
                      kernel-try-lock-u32 kernel-unlock-u32} op)
        (do
          (when-not (= ({'kernel-load-u8 3 'kernel-load-u8-4k 3
                         'kernel-load-u8-16k 3 'kernel-store-u8 4
                         'kernel-store-u8-4k 4 'kernel-subregion 4
                         'kernel-load-u32 3 'kernel-store-u32 4
                         'kernel-try-lock-u32 3 'kernel-unlock-u32 3} op) (count args))
            (reject! "runtime KIR kernel memory operation arity rejected" {:operation op}))
          (doseq [arg args] (verify-expr! arg locals signatures (inc depth) nodes facts)))

        (contains? '#{kernel-boot-info kernel-read-cr0 kernel-write-cr0
                      kernel-read-cr2 kernel-read-cr3 kernel-write-cr3 kernel-invlpg
                      kernel-read-cs kernel-page-fault-handler-address
                      kernel-rt-timer-handler-address
                      kernel-page-fault-recovery-handler-address
                      kernel-configure-page-fault-recovery kernel-load-idt
                      kernel-double-fault-handler-address
                      kernel-configure-double-fault-ist kernel-load-gdt-tss
                      kernel-probe-guard-write kernel-probe-text-write kernel-probe-nx-execute
                      kernel-probe-recoverable-guard-write kernel-probe-double-fault
                      kernel-cli kernel-sti kernel-hlt kernel-pause
                      kernel-out-u8 kernel-out-u32
                      kernel-in-u8 kernel-in-u32
                      kernel-read-msr kernel-write-msr
                      kernel-cpuid-eax kernel-cpuid-ebx
                      kernel-cpuid-ecx kernel-cpuid-edx} op)
        (do
          ;; The port reads take ONE argument -- the port -- where the writes
          ;; take two. Verifying that independently of the frontend is the
          ;; whole point of this table: an emitter handed a two-argument
          ;; `kernel-in-u8` would silently consume something else as the port.
          ;; The MSR pair splits the same way (index / index+value), and the
          ;; consequence of getting it wrong is worse: the second operand of a
          ;; mis-arity'd `kernel-write-msr` is whatever happened to be in the
          ;; register, written into EFER or LSTAR.
          ;;
          ;; The `cpuid` four are arity 2 -- leaf AND subleaf. A one-argument
          ;; one would leave `ecx` holding whatever the leaf expression left
          ;; behind, which for the subleaf-sensitive leaves (0x0d, 0x1f) names
          ;; a DIFFERENT query whose answer is still a plausible-looking
          ;; 32-bit number. That is precisely the failure this independent
          ;; table exists to catch: a wrong arity here does not crash, it
          ;; returns the wrong machine's answer.
          (when-not (= ({'kernel-boot-info 0 'kernel-read-cr0 0 'kernel-write-cr0 1
                         'kernel-read-cr2 0 'kernel-read-cr3 0 'kernel-write-cr3 1
                         'kernel-invlpg 1 'kernel-cli 0 'kernel-sti 0 'kernel-hlt 0
                         'kernel-read-cs 0 'kernel-page-fault-handler-address 0
                         'kernel-rt-timer-handler-address 0
                         'kernel-page-fault-recovery-handler-address 0
                         'kernel-configure-page-fault-recovery 2
                         'kernel-double-fault-handler-address 0
                         'kernel-configure-double-fault-ist 2
                         'kernel-load-gdt-tss 2
                         'kernel-load-idt 2 'kernel-probe-guard-write 0
                         'kernel-probe-text-write 0 'kernel-probe-nx-execute 0
                         'kernel-probe-recoverable-guard-write 0 'kernel-probe-double-fault 0
                         'kernel-pause 0 'kernel-out-u8 2 'kernel-out-u32 2
                         'kernel-in-u8 1 'kernel-in-u32 1
                         'kernel-read-msr 1 'kernel-write-msr 2
                         'kernel-cpuid-eax 2 'kernel-cpuid-ebx 2
                         'kernel-cpuid-ecx 2 'kernel-cpuid-edx 2} op)
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

(defn- entry-result-type? [type]
  (or (contains? entry-result-types type)
      (native-scalar-variant-boundary-type? type)))

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

;; A type an INTERNAL function boundary may carry. Every admitted shape is one
;; machine word, or is boxed into one: the scalar words, an `[:option T]`/
;; `[:result T E]` pair handle, and a record -- which crosses boxed as the pair
;; chain the backends have built since ADR 0062, in BOTH directions now, so a
;; record parameter costs no representation a record result did not already.
;;
;; `[:ref :ns/name]` is admitted, because a signature is the one place it
;; survives lowering and the verified `program` carries no schema table to
;; resolve it against (`program` is `select-keys`-ed to `#{:format :entry
;; :exports :signature :effects :functions}`, and that exact set is what
;; `:kir-sha256` digests -- widening it would move the digest of every module
;; that uses a schema reference, on every target, which is not this change's
;; business).
;;
;; Admitting the NAME is not taking the record on trust. `record-schema-of`
;; binds such a parameter to its reference, and `record-get`'s check then
;; requires the projected schema to be a well-formed `native-scalar-record-type?`
;; whose own name EQUALS that reference -- so projecting schema A through a
;; parameter declared as a reference to B is still rejected, which is the
;; property that matters. A reference that is never projected is simply an
;; opaque word, which is sound because a word is all it can be.
;;
;; A bare `:bool` is admitted here as a PARAMETER type, matching
;; `kotoba.kir/native-boundary-type?` (kotoba-kir ADR 0221). It was withheld for
;; one release cycle, and the reason is worth keeping because it is the reason
;; this predicate is re-derived here at all rather than deferred to kotoba-kir.
;;
;; Withheld (ADR 0001): admitting the type made a latent x86-64 defect
;; REACHABLE. `kotoba.native.x86-64` walked a call's argument list with
;; `(if-let [arg (first remaining)] ...)`, so an argument whose KIR form IS
;; `false` ended the loop and was never emitted -- along with every argument
;; after it -- while the pop sequence still popped the full arity. Measured as
;; real processes: aarch64 correct on all 17 ISA rows, x86-64 SIGILL/SIGSEGV on
;; all 10 rows whose bool argument is written as the literal `false`. AArch64's
;; `mapcat` had no truth test and was unaffected. The type was never the
;; problem -- `:bool` is a plain 0/1 word in both backends, exactly as stated
;; everywhere else in this file -- a Clojure `false`-versus-`nil` conflation in
;; an emitter loop was.
;;
;; Admitted (ADR 0003): kotoba-native `f6f29e9` collapsed all three copies of
;; that walk into one `emit-pushed-arguments` keyed on `(seq remaining)`. The
;; same 17 rows were re-run against it as real x86-64 and aarch64 processes:
;; 17/17 on BOTH ISAs, neither skipped. The rows were falsified against the
;; pre-fix backend in the same session and reproduced all 10 original traps, so
;; they are known to be capable of failing. `deps.edn` pins that backend, which
;; matters here because this file CALLS it (`native-targets` holds
;; `x86-64/emit-program`).
;;
;; One correction that outlived the hold: it is NOT true that "the interpreter
;; validates a `:bool` argument as an i64 word". It validates against the KIR's
;; `:param-types` table, and the trap once cited came from a module carrying no
;; such table -- `invoke-function` defaults an absent one to `:i64` per
;; parameter. That is the compiler's format classification (`typed-values?`
;; excludes `:bool` by name, so a module whose ONLY typed feature is a `:bool`
;; parameter is emitted as `:kotoba.hir/v2` and loses its parameter types). It
;; is a real gap, it is kotoba-kir's, and this predicate never gated it: the
;; caller guards the parameter check with `(contains? function :param-types)`.
;;
;; `:bool` RESULTS were never affected -- `function-result-types` admits them,
;; and the caller checks that first -- nor were `:bool` record fields or
;; `[:option :bool]`, which reach admission by recursion rather than through the
;; removed guard.
(defn- native-boundary-type? [type]
  (or (contains? native-word-field-types type)
      ;; `:bool` reaches admission through the first two clauses --
      ;; `native-word-field-types` and `native-word-value-type?` have both
      ;; listed it since each was written. The removed `(not= :bool type)`
      ;; guard wrapping this `or` was the entire exclusion.
      (native-word-value-type? type)
      (native-scalar-record-type? type)
      (native-scalar-variant-boundary-type? type)
      (and (vector? type) (= 2 (count type)) (= :ref (first type))
           (keyword? (second type)) (some? (namespace (second type))))))

(defn- native-private-handle-type? [type]
  ;; The native context owns these handles. Machine code can forward one
  ;; between private functions as a single word, but the public kexe ABI has
  ;; no operation for a host to construct, validate, inspect, or release one.
  (contains? #{:vector-i64 :vector-f64 :string-index} type))

(defn- native-function-boundary-type? [type exported?]
  (or (native-boundary-type? type)
      (and (not exported?) (native-private-handle-type? type))))

(defn- native-export-copy-result-type? [type]
  ;; The backend/loader copy ABI v1 can marshal only a top-level vector result.
  ;; It does not make a context handle public and does not admit parameters.
  (contains? #{:vector-i64 :vector-f64} type))

;; Each shape condition is named so a rejection can say which one failed. The
;; whole set used to be one `and` reporting `{}`, which meant the most common
;; way to hit it -- an entry returning `:bool` -- surfaced as "module shape
;; rejected" with nothing to go on. A verifier may refuse anything it likes,
;; but it must be possible to learn what it refused.
(def ^:private module-shape-checks
  [[:map (fn [p] (map? p))]
   [:keys (fn [p] (= #{:format :entry :exports :signature :effects :functions} (set (keys p))))]
   [:format (fn [p] (contains? #{:kotoba.kir/v3 :kotoba.kir/v4} (:format p)))]
   ;; A module either has an entry -- `main`, zero-arity, host-readable result
   ;; -- or it is a LIBRARY: no entry, no signature, and an export list that
   ;; names what it offers instead. The library shape is not a weaker version of
   ;; the entry shape; it is a different one, and each of its parts is checked
   ;; as strictly. In particular an entryless module must still export something,
   ;; so "no entry" can never silently mean "no callable surface at all".
   [:entry (fn [p] (or (= 'main (:entry p))
                       (and (nil? (:entry p)) (seq (:exports p)))))]
   [:signature-params (fn [p] (or (nil? (:entry p)) (= [] (:params (:signature p)))))]
   [:signature-result (fn [p] (or (nil? (:entry p))
                                  (entry-result-type? (:result (:signature p)))))]
   [:signature-keys (fn [p] (if (nil? (:entry p))
                              (nil? (:signature p))
                              (= #{:params :result} (set (keys (:signature p))))))]
   [:effects-set (fn [p] (set? (:effects p)))]
   [:effects-valid (fn [p] (every? valid-effect? (:effects p)))]
   [:functions-vector (fn [p] (vector? (:functions p)))]
   [:exports-vector (fn [p] (vector? (:exports p)))]
   [:function-count (fn [p] (<= 1 (count (:functions p)) max-functions))]])

(defn- aggregate-param-locals
  "Parameter schemas used to independently check record projection and
  scalar-variant dispatch."
  [function]
  (let [param-types (:param-types function)]
    (into {}
          (map-indexed (fn [i param]
                         [param (let [t (nth param-types i nil)]
                                  (cond
                                    (native-scalar-variant-boundary-type? t)
                                    (variant-local t)
                                    (or (native-scalar-record-type? t)
                                        (and (vector? t) (= 2 (count t))
                                             (= :ref (first t)) (keyword? (second t))))
                                    t
                                    :else nil))]))
          (:params function))))

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
          exports (set (:exports program))
          signatures
          (into {}
                (map (fn [function]
                       (let [exported? (contains? exports (:name function))]
                         (when-not
                          (and (map? function)
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
                               ;; crosses the boundary boxed as a pair chain --
                               ;; one word, built from the arena primitives
                               ;; already contracted here.
                               (or (contains? function-result-types (:result function))
                                   (and exported?
                                        (not= (:name function) (:entry program))
                                        (empty? (:params function))
                                        (native-export-copy-result-type?
                                         (:result function)))
                                   (native-function-boundary-type?
                                    (:result function) exported?))
                               (or (not (contains? function :param-types))
                                   (and (vector? (:param-types function))
                                        (= (count (:param-types function))
                                           (count (:params function)))
                                        (every?
                                         #(native-function-boundary-type? % exported?)
                                         (:param-types function))))
                               (valid-closure-param-indexes? function)
                               (valid-i64-pair-chain-param-indexes? function)
                               (valid-closure-result-refinement? function)
                               (set? (:effects function))
                               (every? valid-effect? (:effects function)))
                           (reject! "runtime KIR function shape rejected"
                                    {:function (:name function)}))
                         [(:name function) (:params function)]))
                     functions))]
    ;; Identity, in whichever of the two module shapes this is. Both require
    ;; every function name to be distinct and every export to name a function
    ;; that exists; only the entry shape additionally requires `main` to exist,
    ;; be zero-arity, and be exported. The library shape requires a non-empty
    ;; export list in its place -- checked here as well as in
    ;; `module-shape-checks`, since this is where "an export names nothing" is
    ;; caught and a library with no exports would otherwise verify vacuously.
    (when-not (and (= (count functions) (count signatures))
                   (= (count (:exports program)) (count (distinct (:exports program))))
                   (every? #(contains? signatures %) (:exports program))
                   (if (nil? (:entry program))
                     (seq (:exports program))
                     (and (contains? signatures 'main)
                          (empty? (get signatures 'main))
                          (some #{'main} (:exports program)))))
      (reject! "runtime KIR entry or function identity rejected" {}))
    (let [nodes (volatile! 0)
          direct
          (into {}
                (map (fn [function]
                       (let [facts (volatile! {:effects #{} :calls #{}})]
                         ;; A record-typed parameter enters `locals` carrying its
                         ;; declared schema, so `record-schema-of` resolves a
                         ;; projection of it exactly as it resolves one of a
                         ;; `let`-bound record -- and `record-get`'s check still
                         ;; requires the projected schema to EQUAL the declared
                         ;; one. Every other parameter stays nil, as before: a
                         ;; plain word has no schema to carry.
                         (verify-expr! (:body function) (aggregate-param-locals function)
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
                                                  kernel-read-cr0 kernel-write-cr0
                                                  kernel-read-cr3 kernel-write-cr3 kernel-invlpg
                                                  kernel-read-cs kernel-page-fault-handler-address
                                                  kernel-rt-timer-handler-address
                                                  kernel-page-fault-recovery-handler-address
                                                  kernel-configure-page-fault-recovery
                                                  kernel-double-fault-handler-address
                                                  kernel-configure-double-fault-ist
                                                  kernel-load-gdt-tss
                                                  kernel-load-idt kernel-probe-guard-write
                                                  kernel-probe-text-write kernel-probe-nx-execute
                                                  kernel-probe-recoverable-guard-write
                                                  kernel-probe-double-fault
                                                  kernel-cli kernel-sti kernel-hlt kernel-pause
                                                  kernel-out-u8 kernel-out-u32
                                                  kernel-in-u8 kernel-in-u32
                                                  kernel-read-msr kernel-write-msr
                                                  kernel-cpuid-eax kernel-cpuid-ebx
                                                  kernel-cpuid-ecx kernel-cpuid-edx} (first %)))
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
    (let [fuel (:fuel limits)
          _ (when-not (admitted-native-fuel? fuel)
              (reject! "native fuel budget is not admitted"
                       {:target target :fuel fuel :maximum max-native-fuel}))
          expected-fuel-abi (case backend
                              :x86_64-kotoba-v1 {:mode :hidden-context-r9 :initial fuel}
                              :aarch64-kotoba-v1 {:mode :hidden-context-x7 :initial fuel})
          expected-limits {:memory-bytes 65536
                           :fuel fuel
                           :stack-bytes 4096}
          ;; Version 3 added the vector table (offsets 152-192); version 4
          ;; adds `vector-alloc` at 200 and `vector-assoc-in-place` at 208.
          ;; The bump is load-bearing in one direction only, and that is the
          ;; dangerous one: a v3 host has no slots at 200-208, so code
          ;; compiled against v4 that called them would jump through
          ;; uninitialised memory. Every `checked_*` in the loader therefore
          ;; refuses a context whose version is not exactly its own, and this
          ;; map refuses an artifact that names any other ABI -- which is what
          ;; makes the refusal explicit rather than a silent mismatch.
          expected-context {:version 4 :fuel-offset 8 :allow-bitmap-offset 16
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
                            :string-pool-capacity 65536
                            :vector-new-empty-offset 152 :vector-conj-offset 160
                            :vector-count-offset 168 :vector-at-offset 176
                            :vector-assoc-offset 184 :vector-drop-offset 192
                            :vector-alloc-offset 200
                            :vector-assoc-in-place-offset 208
                            ;; Two capacities, because a vector table entry and
                            ;; the elements it spans are separately exhaustible:
                            ;; many small vectors run out of entries first, one
                            ;; growing vector runs out of elements first.
                            :vector-capacity 4096
                            :vector-item-capacity 65536}]
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
                             kernel-boot-info kernel-read-cr0 kernel-write-cr0
                             kernel-read-cr3 kernel-write-cr3 kernel-invlpg
                             kernel-read-cs kernel-page-fault-handler-address
                             kernel-rt-timer-handler-address
                             kernel-page-fault-recovery-handler-address
                             kernel-configure-page-fault-recovery kernel-load-idt
                             kernel-double-fault-handler-address
                             kernel-configure-double-fault-ist kernel-load-gdt-tss
                             kernel-probe-guard-write kernel-probe-text-write kernel-probe-nx-execute
                             kernel-probe-recoverable-guard-write kernel-probe-double-fault
                             kernel-cli kernel-sti kernel-hlt kernel-pause
                             kernel-out-u8 kernel-out-u32
                             kernel-in-u8 kernel-in-u32
                             kernel-read-msr kernel-write-msr
                             ;; The `cpuid` four suppress the oracle here for
                             ;; the same reason `kotoba.kir/lower` lists them:
                             ;; their operands are literals at every real call
                             ;; site, so an oracle has every structural reason
                             ;; to try to evaluate them, and a machine property
                             ;; is not a compile-time value.
                             kernel-cpuid-eax kernel-cpuid-ebx
                             kernel-cpuid-ecx kernel-cpuid-edx}
        kernel-native? (some #(and (seq? %) (contains? kernel-operations (first %)))
                             (tree-seq coll? seq (get-in kexe [:program :functions])))
        expected-value
        ;; The oracle re-executes the ENTRY and requires the sealed value to
        ;; match. A library has no entry to execute, and `kotoba.kir/lower`
        ;; correspondingly seals no value for one, so there is nothing to
        ;; re-derive -- the check below then compares nil to nil, which is the
        ;; honest result rather than a skipped assertion.
        (when (and (empty? effects) (not kernel-native?)
                   (some? (get-in kexe [:program :entry])))
          (try
            (ir/execute (:program kexe) (get-in kexe [:program :entry]) []
                        {:fuel (get-in kexe [:limits :fuel])})
            (catch #?(:clj Exception :cljs :default) error
              (reject! "native artifact oracle evaluation rejected"
                       {:cause (ex-message error)}))))]
    (when-not (= expected-value (:value kexe))
      (reject! "native artifact oracle value rejected" {})))
  kexe)
