(ns kotoba.verifier-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [kotoba.artifact.core :as artifact]
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
      :context-abi {:version 2 :fuel-offset 8 :allow-bitmap-offset 16
                    :allow-bitmap-bytes 32 :cap-call-offset 48
                    :pair-new-offset 56 :pair-first-offset 64
                    :pair-second-offset 72 :pair-capacity 4096
                    :kgraph-assert-offset 80 :kgraph-get-offset 88
                    :kgraph-count-offset 96 :kgraph-entity-at-offset 104
                    :kgraph-capacity 4096
                    :string-equal-offset 112 :string-concat-offset 120
                    :typed-cap-call-offset 128
                    :string-pool-capacity 65536}
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
