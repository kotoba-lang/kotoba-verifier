(ns kotoba.verifier-granted-region-test
  "granted regions: the slice memory family on a NON-aiueos native target.

  Every operation in `kernel-memory-operations` used to require an aiueos
  kernel target, and the reason was sound -- `base` is an address and the
  emitted bounds check constrains the offset within a window, not the window
  itself. What that did not cover is a base the program could not have
  CHOSEN. `kotoba.compiler.frontend`'s region-provenance pass already requires
  every base to flow unmodified from a literal, from `kernel-boot-info`, or
  from a parameter, and already names the case that matters: a tainted
  parameter no internal call supplies is the ABI boundary where the caller
  hands the region in. On a hosted target the caller is the host.

  So this file tests the condition the verifier now attaches to that
  admission, and it re-derives it INDEPENDENTLY of the frontend -- being
  stricter here is sound, trusting the frontend's answer is not.

  ⚠ WHAT THIS FILE CANNOT SAY. It cannot say the admitted program computes
  the right number. That was measured outside this repository on 2026-09-09:
  `amu compile --target aarch64` of a module whose export takes `base` and
  `length` and folds `(slice-of-u8 base length)` was extracted with `amu
  extract-native`, assembled, and CALLED from C with a real buffer and a
  context block carrying fuel at [x7+8]. Four fixtures -- 64 bytes summing to
  2080, a granted length of 10 summing to 55, an empty region, and four 0xFF
  bytes summing to 1020 rather than to a negative -- all correct. That is the
  primitive the provider CLI's `generate!` refuses on today
  (`:kotodama/blocked-on :kotoba/bytes-access`)."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.verifier :as verifier]))

(def ^:private provenance #'verifier/granted-region-provenance)
(def ^:private tainted #'verifier/region-tainted-positions)
(def ^:private granted @#'verifier/granted-region-operations)

(defn- fns [& functions] (vec functions))

;; ---------------------------------------------------------------------------
;; What counts as granted
;; ---------------------------------------------------------------------------

(deftest a-base-that-is-a-parameter-is-granted
  ;; The shape a host-supplied region actually has: the base arrives as a
  ;; parameter and is handed straight to the access.
  (is (nil? (provenance
             (fns {:name 'read-one :params '[base length]
                   :body '(slice-load-u8 base length 0)})))))

(deftest a-literal-base-is-refused
  ;; Legitimate on aiueos, where naming MMIO is the job. On a hosted target it
  ;; is arbitrary memory, and the frontend's provenance rule ADMITS literals --
  ;; so this file has to refuse them itself rather than inherit the answer.
  (is (= 4096 (provenance
               (fns {:name 'read-one :params '[length]
                     :body '(slice-load-u8 4096 length 0)})))))

(deftest a-computed-base-is-refused
  ;; The frontend refuses this too, earlier and with its own message. Asserted
  ;; here anyway: a gate on one route is not a gate, and if the frontend's
  ;; check were ever narrowed this file would still be the one holding.
  (is (some? (provenance
              (fns {:name 'read-one :params '[base length]
                    :body '(slice-load-u8 (+ base 8) length 0)})))))

(deftest every-granted-operation-is-checked-not-just-the-load
  ;; The refusal must reach the whole family, including the store half and the
  ;; narrowing. A family member missing from `region-base-position` would be a
  ;; hole shaped exactly like the one this check exists to close.
  (doseq [op granted]
    (testing (str op)
      (let [args (if (= 'kernel-subregion op) '(4096 len 0 8) '(4096 len 0))]
        (is (= 4096 (provenance (fns {:name 'f :params '[len]
                                      :body (cons op args)})))
            (str op " admitted a literal base"))))))

;; ---------------------------------------------------------------------------
;; Interprocedural -- a slice threaded through a helper is the ordinary case
;; ---------------------------------------------------------------------------

(deftest a-base-passed-into-a-helper-is-tracked
  (let [program (fns {:name 'walk :params '[b l i]
                      :body '(slice-load-u8 b l i)}
                     {:name 'go :params '[base length]
                      :body '(walk base length 0)})]
    (testing "the helper's base position is tainted, and it is position 0"
      (is (= {'walk #{0} 'go #{0}} (select-keys (tainted program) '[walk go]))))
    (testing "and the whole program is granted, because every base is a param"
      (is (nil? (provenance program))))))

(deftest a-caller-that-computes-what-the-helper-uses-as-a-base-is-refused
  ;; The caller is otherwise the hole the callee's own check closed: `walk`
  ;; looks clean in isolation because its base IS a parameter.
  (let [program (fns {:name 'walk :params '[b l i]
                      :body '(slice-load-u8 b l i)}
                     {:name 'go :params '[base length]
                      :body '(walk (+ base 8) length 0)})]
    (is (nil? (provenance (fns (first program))))
        "the callee alone is clean -- which is why the caller must be checked")
    (is (some? (provenance program)))))

(deftest a-caller-that-passes-a-literal-into-a-base-position-is-refused
  (is (some? (provenance
              (fns {:name 'walk :params '[b l i]
                    :body '(slice-load-u8 b l i)}
                   {:name 'go :params '[length]
                    :body '(walk 4096 length 0)})))))

(deftest taint-reaches-through-two-hops
  ;; Fixpoint, not one step: a base threaded through two helpers taints both
  ;; positions and then the entry's own.
  (let [program (fns {:name 'inner :params '[b l i]
                      :body '(slice-load-u8 b l i)}
                     {:name 'middle :params '[b l]
                      :body '(inner b l 0)}
                     {:name 'go :params '[base length]
                      :body '(middle base length)})]
    (is (= {'inner #{0} 'middle #{0} 'go #{0}} (tainted program)))
    (is (nil? (provenance program)))
    (testing "and the two-hop caller is checked, not merely the one-hop"
      (is (some? (provenance
                  (assoc-in program [2 :body] '(middle (+ base 1) length))))))))

;; ---------------------------------------------------------------------------
;; The set itself
;; ---------------------------------------------------------------------------

(deftest the-granted-set-is-the-slice-family-and-the-narrowing
  ;; Named rather than derived from a prefix: a `slice-` operation that is not
  ;; a bounded access must not join this set by being spelled like one.
  (is (= '#{slice-load-u8 slice-load-u16 slice-load-u32 slice-load-u64
            slice-store-u8 slice-store-u16 slice-store-u32 slice-store-u64
            kernel-subregion}
         granted))
  (testing "the byte-WINDOW family is NOT in it"
    ;; That is a surface-size decision and not a property -- a parameter-based
    ;; window would be exactly as safe. Asserted so widening it is deliberate.
    (is (empty? (filter #(= "kernel-load-u8" (name %)) granted)))
    (is (not (contains? granted 'kernel-load-u8)))
    (is (not (contains? granted 'kernel-store-u64-4k)))))
