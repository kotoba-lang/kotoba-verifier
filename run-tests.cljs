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
            [kotoba.verifier-shift-literal-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println (str "\nnbb: " (:test m) " tests, " (:pass m) " passed, "
                (:fail m) " failed, " (:error m) " errors"))
  (when-not (pos? (or (:test m) 0))
    (println "nbb: no tests ran -- that is a failure, not a pass")
    (set! (.-exitCode js/process) 1))
  (when (pos? (+ (or (:fail m) 0) (or (:error m) 0)))
    (set! (.-exitCode js/process) 1)))

(t/run-tests 'kotoba.verifier-shift-literal-test)
