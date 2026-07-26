(ns kotoba.verifier-test
  (:require [clojure.test :refer [deftest is]]
            [kotoba.verifier]))

;; Load gate: the split must not break namespace resolution. Each extracted
;; namespace must load standalone from this repo's own dependency closure.
(deftest every-extracted-namespace-loads
  (is (some? (find-ns 'kotoba.verifier)) "kotoba.verifier must load"))
