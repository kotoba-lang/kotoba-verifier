(ns kotoba.verifier-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [kotoba.artifact.core :as artifact]
            [kotoba.kir]
            [kotoba.kir.compatibility :as compatibility]
            [kotoba.kir.target :as target]
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

(defn- vector-fixture []
  (edn/read-string (slurp (io/resource "conformance/dual-surface-v1.edn"))))

(defn- native-artifact [kir]
  (let [program (select-keys kir [:format :entry :exports :signature
                                  :effects :functions])
        emitted (x86-64/emit-program program)
        profile (target/profile :x86_64-kotoba-v1)]
    (artifact/seal
     {:format :kotoba.kexe/v1
      :target :x86_64-kotoba-v1
      :target-profile profile
      :value nil
      :kir-sha256 (artifact/sha256 program)
      :lowering :runtime-sysv-v1
      :fuel-abi {:mode :hidden-context-r9 :initial 512}
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
       {:hir-format :kotoba.hir/v3 :kir-format :kotoba.kir/v4
        :target :x86_64-kotoba-v1 :target-profile profile
        :value-abi :kotoba.typed/externref-v1})
      :limits {:memory-bytes 65536 :fuel 512 :stack-bytes 4096}
      :code (mapv #(bit-and (int %) 0xff) (:code emitted))
      :program program
      :exports (:exports emitted)})))

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
  ;; ⚠ This gate is NOT landable on its own. `:bool` is admitted here only if
  ;; the 17 ISA rows in ADR 0001 run green on BOTH ISAs -- as of 2026-08-05 they
  ;; do not: x86-64 crashes on every row whose bool argument is the literal
  ;; `false`, because `kotoba.native.x86-64/emit-call` walks its arguments with
  ;; `if-let`. Re-run the rows before merging this branch.
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
    (doseq [types [[:f64] [:f32] [:bytes] [:vector-i64] [:map] ["bool"] [nil]]]
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
;; Agreement with kotoba-kir's independently derived boundary set (ADR 0001)
;; ---------------------------------------------------------------------------

;; This verifier re-derives the native boundary set from `kotoba.kir` ON PURPOSE
;; rather than importing it (ADR 0063), so the two can and do differ. Being
;; stricter is sound -- a verifier can only reject -- but a divergence nobody
;; measures is indistinguishable from one nobody meant, and that is how a
;; `:bool`-parameter module ended up passing `kotoba.kir`'s target selection
;; only to be refused here as "runtime KIR function shape rejected".
;;
;; So the divergence is pinned rather than described. `kotoba.kir` admits a bare
;; `:bool` PARAMETER as of kotoba-kir ADR 0221 (`8de6215`); this verifier does
;; not, and ADR 0001 in this repo records why: on x86-64 the emitted code for a
;; call whose argument is the literal `false` drops that argument and every one
;; after it, because `kotoba.native.x86-64/emit-call` tests its argument list
;; with `if-let`. Measured as real processes on both ISAs -- SIGILL/SIGSEGV on
;; x86-64, correct on aarch64 -- so admitting the type here would ship a
;; boundary that miscompiles rather than one that fails closed.
;;
;; This test is written to FAIL if either side moves: if `kotoba.kir` withdraws
;; `:bool`, or if this predicate is widened without the ADR being revisited.
;; The widening itself is ready on `agent/verifier-bool-boundary-widening`;
;; landing it means flipping this test to agreement in the same commit.
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
