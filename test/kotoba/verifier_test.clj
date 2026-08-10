(ns kotoba.verifier-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [kotoba.artifact.core :as artifact]
            [kotoba.kir]
            [kotoba.kir.compatibility :as compatibility]
            [kotoba.kir.target :as target]
            [kotoba.native.aggregate-abi :as aggregate-abi]
            [kotoba.native.x86-64 :as x86-64]
            [kotoba.verifier]
            [kotoba.verifier.conformance :as conformance]
            [kotoba.verifier.signing]))

;; Load gate: the split must not break namespace resolution. Each extracted
;; namespace must load standalone from this repo's own dependency closure.
(deftest every-extracted-namespace-loads
  (is (some? (find-ns 'kotoba.verifier)) "kotoba.verifier must load")
  (is (some? (find-ns 'kotoba.verifier.signing)) "kotoba.verifier.signing must load")
  (is (some? (find-ns 'kotoba.verifier.conformance))
      "kotoba.verifier.conformance must load"))

(declare native-artifact)

(deftest aggregate-boundary-contract-does-not-widen-verifier-admission
  (let [record-type [:record :t/pair [[:left :i64] [:ready :bool]]]
        plan (aggregate-abi/record-boundary-plan record-type)
        guarantees #{:per-function-frame
                     :spill-live-values-across-call
                     :parallel-argument-assignment
                     :single-word-return-register}]
    (is (= 2 (:abi/version aggregate-abi/contract)))
    (is (= :pair-chain-handle (:boundary/results plan)))
    (is (= :host-context (:boundary/ownership plan)))
    (is (= 4096 (:boundary/arena-cell-limit plan)))
    (is (= :held (:boundary/extracted-admission plan)))
    (is (#'kotoba.verifier/native-boundary-type? record-type)
        "the established boxed record boundary remains independently admitted")
    (is (= :held (get-in aggregate-abi/contract
                         [:extracted :record-boundary])))
    (is (= :held (get-in aggregate-abi/contract
                         [:extracted :variant-boundary])))
    (is (= :scalar-admitted (get-in aggregate-abi/contract
                                    [:extracted :call-admission])))
    (is (= guarantees (get-in aggregate-abi/contract
                              [:extracted :call-requires])))
    (doseq [target [:x86-64 :aarch64]]
      (is (= (aggregate-abi/call-profile target)
             (aggregate-abi/admit-extracted-call! target guarantees)) target)
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"missing-call-guarantees"
           (aggregate-abi/admit-extracted-call!
            target (disj guarantees :spill-live-values-across-call))) target))
    (is (not (#'kotoba.verifier/native-boundary-type?
              [:record :t/duplicate [[:value :i64] [:value :bool]]]))
        "the contract cannot widen the verifier's independently derived set")))

(deftest scalar-direct-call-is-reemitted-by-the-pinned-production-backend
  (let [program {:format :kotoba.kir/v3
                 :entry 'main
                 :exports ['main]
                 :signature {:params [] :result :i64}
                 :effects #{}
                 :functions [{:name 'inc-one
                              :params ['x]
                              :param-types [:i64]
                              :result :i64
                              :effects #{}
                              :body '(+ x 1)}
                             {:name 'main
                              :params []
                              :result :i64
                              :effects #{}
                              :body '(let [live 40]
                                       (+ live (inc-one 1)))}]}
        sealed (native-artifact program)]
    (is (= sealed (kotoba.verifier/verify-artifact! sealed)))
    (is (pos? (get-in sealed [:exports 'main :offset]))
        "the exported entry follows the internal callee in the code image")
    (is (pos? (get-in sealed [:exports 'main :length])))))

(defn- vector-fixture []
  (edn/read-string (slurp (io/resource "conformance/dual-surface-v1.edn"))))

(defn- native-artifact
  ([kir] (native-artifact kir 512))
  ([kir fuel]
  (let [program (select-keys kir [:format :entry :exports :signature
                                  :effects :functions])
        emitted (x86-64/emit-program program)
        profile (target/profile :x86_64-kotoba-v1)]
    (artifact/seal
     {:format :kotoba.kexe/v1
      :target :x86_64-kotoba-v1
      :target-profile profile
      :value (when (and (empty? (:effects program)) (some? (:entry program)))
               (kotoba.kir/execute program (:entry program) [] {:fuel fuel}))
      :kir-sha256 (artifact/sha256 program)
      :lowering :runtime-sysv-v1
      :fuel-abi {:mode :hidden-context-r9 :initial fuel}
      :context-abi {:version 3 :fuel-offset 8 :allow-bitmap-offset 16
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
                    :vector-capacity 4096
                    :vector-item-capacity 65536}
      :effects (:effects program)
      :compatibility
      (compatibility/descriptor
       {:hir-format (if (= :kotoba.kir/v4 (:format program))
                      :kotoba.hir/v3 :kotoba.hir/v2)
        :kir-format (:format program)
        :target :x86_64-kotoba-v1 :target-profile profile
        :value-abi (if (= :kotoba.kir/v4 (:format program))
                     :kotoba.typed/externref-v1 :kotoba.i64/direct-v1)})
      :limits {:memory-bytes 65536 :fuel fuel :stack-bytes 4096}
      :code (mapv #(bit-and (int %) 0xff) (:code emitted))
      :program program
      :exports (:exports emitted)}))))

(deftest bounded-native-fuel-is-an-explicit-matched-artifact-contract
  (let [{:keys [kir]} (vector-fixture)
        raised (native-artifact kir 65536)]
    (is (= raised (kotoba.verifier/verify-artifact! raised)))
    (doseq [[label changed message]
            [[:mismatch
              (artifact/seal (assoc-in raised [:fuel-abi :initial] 65535))
              #"fuel ABI is not admitted"]
             [:zero
              (artifact/seal (-> raised
                                 (assoc-in [:fuel-abi :initial] 0)
                                 (assoc-in [:limits :fuel] 0)))
              #"native fuel budget is not admitted"]
             [:over-maximum
              (artifact/seal (-> raised
                                 (assoc-in [:fuel-abi :initial] 1048577)
                                 (assoc-in [:limits :fuel] 1048577)))
              #"native fuel budget is not admitted"]]]
      (testing (name label)
        (is (thrown-with-msg? clojure.lang.ExceptionInfo message
                              (kotoba.verifier/verify-artifact! changed)))))))

(deftest checked-in-vector-proves-both-surfaces-preserve-one-kir-contract
  (let [{:keys [kir admission expected]} (vector-fixture)
        contract (conformance/kir-contract kir)
        native (native-artifact kir)
        component-surface (assoc contract :admission admission)
        native-surface (assoc contract :admission admission :artifact native)
        result (conformance/verify-dual-surface!
                kir component-surface native-surface)]
    (is (:equivalent? result))
    (is (= (:exports expected) (:exports result)))
    (is (= (:effects expected) (:effects result)))))

(deftest conformance-fails-closed-on-each-shared-dimension
  (let [{:keys [kir admission]} (vector-fixture)
        contract (conformance/kir-contract kir)
        surface (assoc contract :admission admission)]
    (doseq [[label changed]
            [[:exports (update surface :exports conj 'hidden)]
             [:effects (update surface :effects conj [:cap/call 8])]
             [:kir (assoc surface :kir-sha256 (apply str (repeat 64 "0")))]
             [:admission (assoc-in surface [:admission :policy-id] :other)]]]
      (testing (name label)
        (is (thrown? clojure.lang.ExceptionInfo
                     (conformance/verify-dual-surface!
                      kir surface changed)))))))

;; ---------------------------------------------------------------------------
;; Module shape rejections name the condition that failed
;; ---------------------------------------------------------------------------

(def ^:private ok-program
  {:format :kotoba.kir/v3 :entry 'main :exports ['main]
   :signature {:params [] :result :i64} :effects #{}
   :functions [{:name 'main :params [] :result :i64 :effects #{} :body 1}]})

(defn- shape-condition [program]
  (try (#'kotoba.verifier/verify-program! program) nil
       (catch clojure.lang.ExceptionInfo e
         (when (= "runtime KIR module shape rejected" (ex-message e))
           (:condition (ex-data e))))))

(deftest a-module-shape-rejection-names-the-failing-condition
  ;; The whole set used to be one `and` reporting `{}`. A verifier may refuse
  ;; anything it likes, but it must be possible to learn what it refused --
  ;; without this, the most common way to hit the check (an entry returning a
  ;; comparison, hence `:bool`) was indistinguishable from a malformed module.
  (is (nil? (shape-condition ok-program)) "the reference program must verify")
  (is (= :entry (shape-condition (assoc ok-program :entry 'not-main))))
  (is (= :format (shape-condition (assoc ok-program :format :kotoba.kir/v9))))
  (is (= :keys (shape-condition (assoc ok-program :extra 1))))
  (is (= :signature-result
         (shape-condition (assoc ok-program :signature {:params [] :result :string})))
      "an unsupported entry result must be reported as such, not as a shapeless failure")
  (is (= :function-count (shape-condition (assoc ok-program :functions []))))
  (is (= :exports-vector (shape-condition (assoc ok-program :exports #{'main}))))
  (is (= :map (shape-condition "not a program"))
      "a non-map must fail the first condition rather than throw"))

;; ---------------------------------------------------------------------------
;; vector-i64 / vector-f64 (ADR-2608030300)
;; ---------------------------------------------------------------------------

(defn- verifies? [body]
  (try (#'kotoba.verifier/verify-program!
        (assoc-in ok-program [:functions 0 :body] body))
       true
       (catch clojure.lang.ExceptionInfo _ false)))

(defn- rejection [body]
  (try (#'kotoba.verifier/verify-program!
        (assoc-in ok-program [:functions 0 :body] body))
       nil
       (catch clojure.lang.ExceptionInfo e (ex-message e))))

(deftest both-vector-families-are-admitted-at-their-kir-arities
  (doseq [body ['(vector-new)
                '(vector-new 1 2 3)
                '(vector-count (vector-new 1))
                '(vector-at (vector-new 1) 0)
                '(vector-get (vector-new 1) 0 7)
                '(vector-assoc (vector-new 1) 0 2)
                '(vector-conj (vector-new 1) 2)
                '(vector-drop (vector-new 1) 1)
                '(vector-f64-new)
                '(vector-f64-count (vector-f64-new 1))
                '(vector-f64-at (vector-f64-new 1) 0)
                '(vector-f64-get (vector-f64-new 1) 0 7)
                '(vector-f64-assoc (vector-f64-new 1) 0 2)
                '(vector-f64-conj (vector-f64-new 1) 2)
                '(vector-f64-drop (vector-f64-new 1) 1)]]
    (testing (str body)
      (is (verifies? body)))))

;; The arity table is the point: an operation admitted at the wrong arity
;; would reach a backend that reads an argument which is not there.
(deftest a-wrong-vector-arity-is-rejected-and-says-which-operation
  (doseq [body ['(vector-count)
                '(vector-count (vector-new 1) 2)
                '(vector-at (vector-new 1))
                '(vector-get (vector-new 1) 0)
                '(vector-assoc (vector-new 1) 0)
                '(vector-conj (vector-new 1))
                '(vector-drop (vector-new 1))
                '(vector-f64-at (vector-f64-new 1))]]
    (testing (str body)
      (is (= "runtime KIR vector operation arity rejected" (rejection body))))))

;; `vector-new` is the one variadic operation, so its bound is its element
;; count rather than an arity. Checked here because nothing downstream would
;; catch it: the native lowering expands one host call per element, so an
;; unbounded literal is an unbounded expansion.
(deftest a-vector-literal-past-the-item-limit-is-rejected
  (is (verifies? (cons 'vector-new (repeat 16384 1))))
  (is (= "runtime KIR vector literal exceeds the item limit"
         (rejection (cons 'vector-new (repeat 16385 1)))))
  (is (= "runtime KIR vector literal exceeds the item limit"
         (rejection (cons 'vector-f64-new (repeat 16385 1))))))

(deftest closure-parameter-refinement-is-checked
  (let [consumer {:name 'consume :params ['closure] :param-types [:i64]
                  :closure-param-indexes [0]
                  :result :i64 :effects #{} :body 'closure}
        program (update ok-program :functions conj consumer)]
    (is (= program (#'kotoba.verifier/verify-program! program)))
    (doseq [indexes [[1] [0 0] [0 -1] ["0"]]]
      (testing (pr-str indexes)
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
             (#'kotoba.verifier/verify-program!
              (assoc-in program [:functions 1 :closure-param-indexes] indexes))))))
    (testing "the refined parameter keeps its i64 ABI type"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
           (#'kotoba.verifier/verify-program!
            (assoc-in program [:functions 1 :param-types] [:string])))))))

(deftest closure-result-refinement-is-checked
  (let [maker {:name 'make :params [] :param-types []
               :closure-result? true
               :result :i64 :effects #{} :body 0}
        program (update ok-program :functions conj maker)]
    (is (= program (#'kotoba.verifier/verify-program! program)))
    (doseq [value [false 1 :yes]]
      (testing (pr-str value)
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
             (#'kotoba.verifier/verify-program!
              (assoc-in program [:functions 1 :closure-result?] value))))))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
         (#'kotoba.verifier/verify-program!
          (assoc-in program [:functions 1 :result] :string))))))

(deftest i64-pair-chain-parameter-refinement-is-checked
  (let [consumer {:name 'consume :params ['args] :param-types [:i64]
                  :i64-pair-chain-param-indexes [0]
                  :result :i64 :effects #{} :body 'args}
        program (update ok-program :functions conj consumer)]
    (is (= program (#'kotoba.verifier/verify-program! program)))
    (doseq [indexes [[1] [0 0] [0 -1] ["0"]]]
      (testing (pr-str indexes)
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
             (#'kotoba.verifier/verify-program!
              (assoc-in program [:functions 1 :i64-pair-chain-param-indexes]
                        indexes))))))
    (testing "the refined parameter keeps its i64 ABI type"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
           (#'kotoba.verifier/verify-program!
            (assoc-in program [:functions 1 :param-types] [:string])))))
    (testing "pair-chain and closure refinements cannot overlap"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"runtime KIR function shape rejected"
           (#'kotoba.verifier/verify-program!
            (assoc-in program [:functions 1 :closure-param-indexes] [0])))))))

(deftest a-bool-entry-result-is-admitted
  ;; kotoba-kir 38d1bd0 (2026-07-31) decided the value LEAVING a target is a
  ;; host boolean, and wasm/ESM/reference all box one. Native was the target
  ;; not yet carried across. What blocked it was kotoba.kir/lower's oracle fold
  ;; guard being :i64-only -- nothing was sealed for a :bool entry, so the
  ;; oracle check had nothing to compare against, and widening this set alone
  ;; would have changed nothing. lower now folds and seals the boxed boolean.
  (is (nil? (shape-condition (assoc ok-program :signature {:params [] :result :bool}))))
  (is (nil? (shape-condition ok-program)))
  (testing "a result type outside the pair is still rejected, and says so"
    (is (= :signature-result
           (shape-condition (assoc ok-program :signature {:params [] :result :string}))))))

(defn- function-rejected?
  "True when PROGRAM fails specifically the FUNCTION shape check. Named rather
  than reusing `verifies?` because the whole hazard here is a test that goes
  green while some OTHER check is what rejected -- or admitted -- the input.
  Anything but the function-shape rejection is reported as a distinct value, so
  a row can never pass by being refused for an unrelated reason."
  [program]
  (try (#'kotoba.verifier/verify-program! program) false
       (catch clojure.lang.ExceptionInfo e
         (if (= "runtime KIR function shape rejected" (ex-message e))
           true
           [:other (ex-message e)]))))

(defn- with-param-types
  "`ok-program` plus one helper function carrying PARAM-TYPES. Every other part
  of the helper is deliberately boring -- an i64 result, no effects, a body that
  is just the first parameter -- so the ONLY thing that can decide the outcome
  is the parameter-type check."
  [param-types]
  (update ok-program :functions conj
          {:name 'helper
           :params (vec (map-indexed (fn [i _] (symbol (str "p" i))) param-types))
           :param-types (vec param-types)
           :result :i64 :effects #{}
           :body (if (seq param-types) 'p0 0)}))

(deftest a-bool-parameter-is-admitted-at-a-function-boundary
  ;; This gate is admission only. What justifies it is EXECUTION: the 17 ISA
  ;; rows in ADR 0003, run as real x86-64 and aarch64 processes against
  ;; kotoba-native `f6f29e9`, 17/17 on both. Before that backend fix the same
  ;; rows trapped on all 10 x86-64 rows whose bool argument is the literal
  ;; `false` (ADR 0001), which is why this predicate was held for a cycle.
  ;;
  ;; Only the BARE-`:bool` rows below are gates for the guard removal. The
  ;; wrapped and record-field rows are documentation: they reach admission by
  ;; recursion through `native-word-value-type?` and passed before the change
  ;; too. Measured by restoring the guard -- 8 assertions move, and those are
  ;; the bare rows plus the kotoba-kir agreement flip.
  (testing "alone"
    (is (false? (function-rejected? (with-param-types [:bool])))))
  (testing "alongside the other admitted boundary types, in both orders"
    (doseq [types [[:string :bool] [:bool :string]
                   [:i64 :bool] [:bool :i64]
                   [:keyword :bool] [:bool :bool]]]
      (testing (pr-str types)
        (is (false? (function-rejected? (with-param-types types)))))))
  (testing "wrapped, where `native-word-value-type?` already recursed into it"
    (doseq [types [[[:option :bool]] [[:result :bool :i64]] [[:result :i64 :bool]]]]
      (testing (pr-str types)
        (is (false? (function-rejected? (with-param-types types)))))))
  (testing "as a record field, which never depended on this predicate"
    (is (false? (function-rejected?
                 (with-param-types [[:record :t/r [[:a :bool] [:b :i64]]]])))))
  ;; The negative half. Widening one type must not have widened the set: these
  ;; are rejected before and after, and if any of them started passing the gate
  ;; would have stopped being a gate.
  (testing "types outside the one-word slice are still refused"
    (doseq [types [[:f64] [:f32] [:bytes] [:map] ["bool"] [nil]]]
      (testing (pr-str types)
        (is (true? (function-rejected? (with-param-types types)))))))
  (testing "a malformed parameter-type table is still refused"
    (is (true? (function-rejected?
                (assoc-in (with-param-types [:bool]) [:functions 1 :param-types]
                          [:bool :bool])))
        "the table must still match the parameter count")
    (is (true? (function-rejected?
                (assoc-in (with-param-types [:bool]) [:functions 1 :param-types]
                          '(:bool))))
        "the table must still be a vector")))

(deftest native-vector-handles-are-private-function-boundaries-only
  (doseq [vector-type [:vector-i64 :vector-f64]]
    (testing (name vector-type)
      (let [private-helper (-> (with-param-types [vector-type])
                               (assoc-in [:functions 1 :result] vector-type))]
        (is (false? (function-rejected? private-helper))
            "a private native call carries the context-owned handle as one word")
        (is (true? (function-rejected?
                    (update private-helper :exports conj 'helper)))
            "a kexe export cannot accept or return an unmarshalable handle")))))

(deftest native-string-index-is-private-and-its-operations-are-sealed
  (let [private-helper (-> (with-param-types [:string-index])
                           (assoc-in [:functions 1 :result] :string-index))]
    (is (false? (function-rejected? private-helper)))
    (is (true? (function-rejected?
                (update private-helper :exports conj 'helper)))))
  (doseq [form ['(string-index-new)
                '(string-index-count (string-index-new))
                '(string-index-contains (string-index-new) "cid")
                '(string-index-get (string-index-new) "cid")
                '(string-index-assoc (string-index-new) "cid" 7)]]
    (is (verifies? form) (pr-str form)))
  (doseq [form ['(string-index-new 1)
                '(string-index-count)
                '(string-index-contains index)
                '(string-index-get index key extra)
                '(string-index-assoc index key)]]
    (is (= "runtime KIR string-index operation arity rejected"
           (rejection form))
        (pr-str form))))

(deftest a-sealed-native-artifact-reemits-string-index-without-a-new-abi
  (let [program (-> ok-program
                    (assoc :format :kotoba.kir/v4)
                    (assoc-in [:functions 0 :body]
                              '(string-index-count
                                (string-index-assoc
                                 (string-index-new) "cid" 7))))
        artifact (artifact/seal (assoc (native-artifact program) :value 1))]
    (is (= 3 (get-in artifact [:context-abi :version])))
    (is (= artifact (kotoba.verifier/verify-artifact! artifact)))))

(deftest a-bool-parameter-refinement-is-still-i64-only
  ;; `:closure-param-indexes` / `:i64-pair-chain-param-indexes` name parameters
  ;; that must be raw i64 words, and both check `param-types` themselves. A
  ;; wider boundary type must not leak into them: a closure handle is not a
  ;; boolean, and calling one that is would be a jump through a 0/1 word.
  (let [program (with-param-types [:bool])]
    (doseq [k [:closure-param-indexes :i64-pair-chain-param-indexes]]
      (testing (name k)
        (is (true? (function-rejected? (assoc-in program [:functions 1 k] [0]))))))))

;; ---------------------------------------------------------------------------
;; Agreement with kotoba-kir's independently derived boundary set (ADR 0003)
;; ---------------------------------------------------------------------------

;; This verifier re-derives the native boundary set from `kotoba.kir` ON PURPOSE
;; rather than importing it (ADR 0063), so the two can and do differ. Being
;; stricter is sound -- a verifier can only reject -- but a divergence nobody
;; measures is indistinguishable from one nobody meant, and that is how a
;; `:bool`-parameter module ended up passing `kotoba.kir`'s target selection
;; only to be refused here as "runtime KIR function shape rejected".
;;
;; That divergence is now CLOSED: both sides admit a bare `:bool` PARAMETER --
;; `kotoba.kir` since its ADR 0221 (`8de6215`), this verifier since ADR 0003,
;; once kotoba-native `f6f29e9` fixed the x86-64 argument walk that made the
;; type unsafe to admit (ADR 0001). Re-derivation is still the point: the whole
;; reason this repo could hold the type for a cycle is that it does not import
;; kotoba-kir's answer.
;;
;; This test is written to FAIL if either side moves, in either direction, so
;; the next person to change either predicate finds the ADRs rather than a
;; miscompile.
(deftest the-native-boundary-set-agrees-with-kotoba-kirs
  (let [kir-admits? (fn [type] (boolean (#'kotoba.kir/native-boundary-type? type {})))
        ours? (fn [type] (boolean (#'kotoba.verifier/native-boundary-type? type)))]
    (testing "every other boundary type agrees, so the divergence is exactly one type"
      (doseq [type [:i64 :string :keyword
                    [:option :bool] [:option :i64] [:result :bool :i64]
                    [:record :t/r [[:a :bool] [:b :i64]]]
                    :f64 :f32 :bytes :map :vector-i64 nil "bool"]]
        (testing (pr-str type)
          (is (= (kir-admits? type) (ours? type))
              (str "kotoba.kir " (if (kir-admits? type) "admits" "refuses")
                   " " (pr-str type) " and this verifier does not agree")))))
    ;; On this branch the divergence is CLOSED: both sides admit `:bool`. On
    ;; `main` this asserts the opposite, and ADR 0001 says why. Landing this
    ;; branch means landing this flip in the same commit as the predicate.
    (testing "a bare :bool parameter now agrees too"
      (is (true? (kir-admits? :bool)))
      (is (true? (ours? :bool))))
    ;; `:bool` is admitted in every position that is NOT a bare parameter, and
    ;; always was. Held here so the ADR's scope cannot be misread as "native
    ;; cannot carry a bool".
    (testing ":bool is unaffected everywhere it already worked"
      (is (nil? (shape-condition (assoc ok-program :signature {:params [] :result :bool})))
          "as an entry result")
      (is (true? (ours? [:option :bool])) "wrapped in an option")
      (is (true? (ours? [:record :t/r [[:a :bool] [:b :i64]]])) "as a record field"))))

;; ---------------------------------------------------------------------------
;; A projection over a boxed record HANDLE (ADR 0004).
;;
;; A record that crosses a function boundary is boxed into a one-word pair
;; chain. Reading a field back off that word is the same walk whether the word
;; was projected on the spot or named by a `let` first, and whether the callee's
;; result was declared expanded or by schema reference -- the backends do not
;; distinguish any of it. This verifier did, and that is what these rows pin.

(def ^:private rec '[:record :t/r [[:a :i64] [:b :i64]]])
(def ^:private rec-ref '[:ref :t/r])
(def ^:private other-rec '[:record :t/other [[:a :i64] [:b :i64]]])

(defn- handle-program
  "`ok-program` plus a `mk` declared to return RESULT, and a `main` whose body
  is BODY. RESULT is the only thing that varies between the expanded and the
  by-reference spelling, so nothing else can decide the outcome."
  [result body]
  (-> ok-program
      (assoc-in [:functions 0 :body] body)
      (update :functions conj
              {:name 'mk :params [] :result result :effects #{}
               :body (list 'record-new rec 4 9)})))

(defn- handle-outcome
  "nil when the program verifies, else the rejection message. Named rather than
  a boolean so a row can never go green because some OTHER check refused the
  input -- the hazard this whole area has."
  [result body]
  (try (#'kotoba.verifier/verify-program! (handle-program result body)) nil
       (catch clojure.lang.ExceptionInfo e (ex-message e))))

(deftest a-let-bound-boxed-handle-may-be-projected
  ;; `(let [h (mk)] (record-get … h :b))` -- murakumo's `infer_plan_core`,
  ;; `infer_schedule_core` and `task_plan_core` all read a multi-field result
  ;; this way, and it was the last shape in those three with no native lowering.
  ;;
  ;; Both fields are exercised on purpose. A chain walked to the wrong depth
  ;; still yields a plausible i64, so a row that only ever selected `:a` would
  ;; pass even when the walk is wrong; this gate cannot see depth at all, but
  ;; the rows it shares with kotoba-native's execution table can, and they are
  ;; kept the same shape deliberately.
  (doseq [result [rec rec-ref]
          field [:a :b]]
    (testing (str (pr-str result) " / " field)
      (is (nil? (handle-outcome result (list 'let ['h '(mk)]
                                             (list 'record-get rec 'h field))))))))

(deftest a-handle-projected-straight-off-the-call-may-be-declared-by-reference
  ;; The second shape, and the one that had nothing to do with `let`:
  ;; `(record-get … (mk) :b)` where `mk`'s result is `[:ref :t/r]` was refused
  ;; while the identical program with the result written inline was admitted.
  ;; `record-schema-of` resolved the call and then demanded
  ;; `native-scalar-record-type?`, which a reference is not.
  (doseq [field [:a :b]]
    (testing (str "expanded / " field)
      (is (nil? (handle-outcome rec (list 'record-get rec '(mk) field)))))
    (testing (str "by reference / " field)
      (is (nil? (handle-outcome rec-ref (list 'record-get rec '(mk) field)))))))

(deftest a-handle-projected-twice-at-different-depths-is-admitted
  (doseq [result [rec rec-ref]]
    (testing (pr-str result)
      (is (nil? (handle-outcome
                 result
                 (list 'let ['h '(mk)]
                       (list '- (list 'record-get rec 'h :a)
                             (list 'record-get rec 'h :b)))))))))

(deftest projecting-the-wrong-schema-through-a-handle-is-still-rejected
  ;; The property that makes admitting a reference BY NAME sound rather than
  ;; trusting. A reference carries no field list, so the name is the whole
  ;; check: a result declared `[:ref :t/r]` may not be projected as `:t/other`,
  ;; even though both records have the same arity and field names and would
  ;; therefore walk to a valid-looking depth.
  (doseq [[why body]
          [["let-bound" (list 'let ['h '(mk)] (list 'record-get other-rec 'h :b))]
           ["straight off the call" (list 'record-get other-rec '(mk) :b)]]]
    (testing why
      (is (= "runtime KIR record projection rejected"
             (handle-outcome rec-ref body))
          "a reference to :t/r projected as :t/other")
      (is (= "runtime KIR record projection rejected"
             (handle-outcome rec body))
          "an expanded :t/r projected as :t/other"))))

(deftest a-let-bound-non-record-is-still-not-projectable
  ;; Widening which BINDINGS carry a schema must not make every binding
  ;; projectable. A slot holding an ordinary i64 is one word too, and walking it
  ;; as a pair chain would read the arena at an address that is really a number.
  (is (= "runtime KIR record projection rejected"
         (handle-outcome rec (list 'let ['h 7] (list 'record-get rec 'h :b)))))
  ;; A call whose result is NOT a record is the same hazard by another route.
  (is (= "runtime KIR record projection rejected"
         (handle-outcome :i64 (list 'let ['h '(mk)] (list 'record-get rec 'h :b))))))

(deftest a-flattened-record-forwarded-through-a-second-binding-is-still-rejected
  ;; Deliberately NOT admitted: a `let`-bound `record-new` is flattened into one
  ;; slot per field, so rebinding it is N slots being read as one word, which
  ;; both backends refuse. This gate stays exactly as wide as the emitter it
  ;; re-derives -- `binding-record-schema` resolves a `record-new` and a call,
  ;; and deliberately not a bare symbol.
  (is (= "runtime KIR record projection rejected"
         (handle-outcome rec (list 'let ['r (list 'record-new rec 4 9) 'r2 'r]
                                   (list 'record-get rec 'r2 :b))))))

(deftest a-same-schema-scalar-record-if-may-be-bound-and-projected
  (let [record-if (list 'if 1
                        (list 'record-new rec 1 2)
                        (list 'record-new rec 3 4))]
    (doseq [field [:a :b]]
      (is (nil? (handle-outcome
                 rec
                 (list 'let ['r record-if]
                       (list 'record-get rec 'r field))))))))

(deftest a-same-schema-scalar-record-if-may-be-projected-directly
  (let [record-if (list 'if 1
                        (list 'record-new rec 1 2)
                        (list 'record-new rec 3 4))]
    (doseq [field [:a :b]]
      (is (nil? (handle-outcome rec
                                (list 'record-get rec record-if field)))))))

(deftest record-sroa-binding-shape-stays-fail-closed
  (let [string-rec '[:record :t/string-pair [[:a :string] [:b :i64]]]
        nested-rec [:record :t/nested [[:a rec] [:b :i64]]]]
    (doseq [[why projected-type record-if]
            [["different branch schemas"
              rec
              (list 'if 1
                    (list 'record-new rec 1 2)
                    (list 'record-new other-rec 3 4))]
             ["string field"
              string-rec
              (list 'if 1
                    (list 'record-new string-rec "a" 2)
                    (list 'record-new string-rec "b" 4))]
             ["nested record field"
              nested-rec
              (list 'if 1
                    (list 'record-new nested-rec (list 'record-new rec 1 2) 3)
                    (list 'record-new nested-rec (list 'record-new rec 4 5) 6))]]]
      (testing why
        (is (= "runtime KIR record projection rejected"
               (handle-outcome rec
                               (list 'let ['r record-if]
                                     (list 'record-get projected-type 'r :b)))))))))

(def ^:private scalar-variant
  '[:variant :t/value [[:number :i64] [:flag :bool]]])
(def ^:private other-variant
  '[:variant :t/other [[:number :i64] [:flag :bool]]])

(defn- variant-outcome [body]
  (try (#'kotoba.verifier/verify-program!
        (assoc-in ok-program [:functions 0 :body] body))
       nil
       (catch clojure.lang.ExceptionInfo e (ex-message e))))

(defn- match-variant [value]
  (list 'variant-match scalar-variant value
        [[:number 'payload (list '+ 'payload 1)]
         [:flag 'payload (list 'if 'payload 1 7)]]))

(deftest a-local-scalar-variant-may-be-constructed-bound-and-matched
  (doseq [constructor [(list 'variant-new scalar-variant :number 41)
                       (list 'variant-new scalar-variant :flag false)]]
    (is (nil? (variant-outcome
               (list 'let ['v constructor] (match-variant 'v)))))))

(deftest a-same-schema-scalar-variant-if-may-be-matched
  (let [variant-if (list 'if 1
                         (list 'variant-new scalar-variant :number 41)
                         (list 'variant-new scalar-variant :flag false))]
    (is (nil? (variant-outcome (match-variant variant-if))))
    (is (nil? (variant-outcome
               (list 'let ['v variant-if] (match-variant 'v)))))))

(deftest variant-sroa-admission-stays-fail-closed
  (let [string-variant '[:variant :t/string [[:number :i64] [:text :string]]]]
    (testing "symbol forwarding"
      (is (= "runtime KIR variant dispatch rejected"
             (variant-outcome
              (list 'let ['v (list 'variant-new scalar-variant :number 1)
                          'v2 'v]
                    (match-variant 'v2))))))
    (testing "different branch schemas"
      (is (= "runtime KIR variant dispatch rejected"
             (variant-outcome
              (match-variant
               (list 'if 1
                     (list 'variant-new scalar-variant :number 1)
                     (list 'variant-new other-variant :flag false)))))))
    (testing "non-scalar local payload family"
      (is (= "runtime KIR variant dispatch rejected"
             (variant-outcome
              (list 'let ['v (list 'variant-new string-variant :text "x")]
                    (list 'variant-match string-variant 'v
                          [[:number 'x 'x] [:text 'x 0]]))))))
    (testing "reordered branches"
      (is (= "runtime KIR variant dispatch rejected"
             (variant-outcome
              (list 'variant-match scalar-variant
                    (list 'variant-new scalar-variant :number 1)
                    [[:flag 'x 0] [:number 'x 'x]])))))))

(deftest an-undeclared-field-is-still-rejected-through-a-handle
  (doseq [result [rec rec-ref]]
    (is (= "runtime KIR record projection rejected"
           (handle-outcome result (list 'let ['h '(mk)]
                                        (list 'record-get rec 'h :nope)))))))
