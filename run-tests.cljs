(ns run-tests
  "The portable slice of the verifier on nbb -- the JDK-free compiler host.

   nbb --classpath \"src:test:$(clojure -Spath -M:test)\" run-tests.cljs

   This repository had only `clojure -M:test` until 2026-09-02. A verifier
   whose whole job is to re-derive a rule independently was being exercised on
   one of the two hosts that run it, and the half that was never run refused
   every artifact using an i64 or i32 shift -- because a guest literal is a
   JavaScript `bigint` there and the gate was spelled with `integer?`. Neither
   the JVM suite nor the JVM route of `bin/amu` could see it.

   Namespaces listed here must be `.cljc`. Adding a `.clj`-only test to this
   list is how the list quietly stops meaning what it says."
  (:require [cljs.test :as t]
            [kotoba.verifier-shift-literal-test]
            ;; signing moved from .clj to .cljc on 2026-09-08; this is the
            ;; half that checks the JVM's bytes from the Node side.
            [kotoba.verifier-signing-parity-test]
            ;; the first test that verifies a real native artifact on this host
            [kotoba.verifier-native-artifact-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println (str "\nnbb: " (:test m) " tests, " (:pass m) " passed, "
                (:fail m) " failed, " (:error m) " errors"))
  (when-not (pos? (or (:test m) 0))
    (println "nbb: no tests ran -- that is a failure, not a pass")
    (set! (.-exitCode js/process) 1))
  (when (pos? (+ (or (:fail m) 0) (or (:error m) 0)))
    (set! (.-exitCode js/process) 1)))

;; Every namespace in the :require list above, not one of them.
;;
;; This line named a single namespace until 2026-09-08, so being in that list
;; was decoration: `kotoba.verifier-signing-parity-test` was added, the suite
;; reported the same 8 tests and 91 assertions it had before, and nothing said
;; a test had not run. The docstring above warns that adding a `.clj`-only
;; test is "how the list quietly stops meaning what it says" -- the list had
;; already stopped meaning it, in the other direction.
(t/run-tests 'kotoba.verifier-shift-literal-test
             'kotoba.verifier-signing-parity-test
             'kotoba.verifier-native-artifact-test)
