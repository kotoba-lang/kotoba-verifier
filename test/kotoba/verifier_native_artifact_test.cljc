(ns kotoba.verifier-native-artifact-test
  "A real native artifact, verified on whichever host is running.

  `amu verify` was a `.clj`-only command until 2026-09-08, so nothing
  JVM-free ever called `verify-artifact!` on a native artifact. Two gates in
  this verifier had therefore never been executed on the cljs host, and both
  were wrong there:

    malformed code bytes            the byte gate was spelled `integer?`, and
                                    a byte read back out of an artifact is a
                                    JavaScript bigint -- so EVERY native
                                    artifact was refused
    native artifact oracle value    the sealed value came back a Number and
      rejected                      the oracle re-derivation a BigInt, and
                                    (= 42 (js/BigInt 42)) is false

  This file is in BOTH suites, so neither host can drift again without
  something going red. The fixture is a real `aarch64-macos` artifact built
  by `amu compile --module-lock --blocks --jvm-free`, whose `main` the
  measured kexe_loader answers 42 for."
  (:require [clojure.test :as t :refer [deftest is testing]]
            [clojure.edn :as edn]
            [kotoba.verifier :as verifier]
            #?(:clj [clojure.java.io :as io])
            #?(:cljs ["node:fs" :as fs])
            #?(:cljs ["node:path" :as path])))

(defn- guest-numbers
  "What the COMPILER HOST hands this verifier, which is not what
  `clojure.edn/read-string` hands it.

  Measured 2026-09-08: amu's own reader produces a JavaScript bigint for an
  artifact's integer, and `clojure.edn/read-string` produces a plain Number
  for a small one. A fixture read with the latter therefore passes an
  `integer?` gate that the real path fails, and a test built on it looks like
  it covers the bug while covering nothing. Both gates below were reverted to
  `integer?` against the plain-Number fixture and the suite stayed green.

  So the fixture is coerced to the representation the real caller uses."
  [artifact]
  #?(:clj artifact
     :cljs (letfn [(walk [v]
                     (cond
                       (and (number? v) (js/Number.isInteger v)) (js/BigInt v)
                       (map? v) (into (empty v) (map (fn [[k x]] [k (walk x)])) v)
                       (vector? v) (mapv walk v)
                       (set? v) (into #{} (map walk) v)
                       :else v))]
             ;; DEEP, because a shallow coercion is how this fixture lied
             ;; once already: coercing only :code and :value left
             ;; [:limits :fuel] a plain number, `kotoba.kir` accepted it, the
             ;; artifact verified, and the test reported the chain as
             ;; finished when the real path was still refused at the fuel
             ;; gate. amu's reader makes EVERY integer a bigint.
             (walk artifact))))

(defn- fixture []
  (guest-numbers
   (edn/read-string
    #?(:clj (slurp (io/resource "fixtures/aarch64-demo.kexe"))
       :cljs (fs/readFileSync (path/join "resources" "fixtures" "aarch64-demo.kexe") "utf8")))))

(deftest the-gates-fixed-here-no-longer-refuse
  ;; Each of these had its own refusal on the cljs host, in this order, and
  ;; each is now past. The artifact is NOT fully verified on cljs yet -- see
  ;; the test below, which names what is still in the way -- so this asserts
  ;; what was fixed and nothing more.
  (let [artifact (fixture)
        refusal (try (verifier/verify-artifact! artifact) nil
                     (catch #?(:clj Throwable :cljs :default) e (ex-message e)))]
    (is (not= "malformed code bytes" refusal))
    (is (not= "native artifact oracle value rejected" refusal))
    (is (not= "native instruction stream rejected" refusal))
    (is (not= "native export table rejected" refusal))))

(deftest the-code-bytes-gate-still-refuses
  (testing "the assertions above are not accepting everything"
    (is (thrown? #?(:clj Exception :cljs :default)
                 (verifier/verify-artifact!
                  (assoc (fixture) :code [#?(:clj 999 :cljs (js/BigInt 999))]))))
    (is (thrown? #?(:clj Exception :cljs :default)
                 (verifier/verify-artifact! (assoc (fixture) :code []))))))

;; No "this fixture fully verifies on the JVM" test, and the reason is
;; measured rather than assumed: HEAD refuses it with "native target profile
;; does not match target identity". The artifact was built by an `amu` that
;; pinned an earlier commit of THIS repository, so its `:target-profile` and
;; this verifier's expectation have skewed. That is a fixture-vintage fact,
;; not something the changes here cause or could fix, and asserting around it
;; would have meant weakening a profile check to make a test green.

#?(:cljs
   (deftest a-real-native-artifact-verifies-on-this-host
     ;; The chain finished on 2026-09-08. Six refusals, one cause each, none
     ;; ever seen because `amu verify` was a `.clj`-only command: the byte
     ;; gate's `integer?`, three structural comparisons between a re-derived
     ;; value and a sealed one, the fuel gate, and the fuel counter's
     ;; bigint/number mix. This is the whole artifact, verified.
     (is (map? (verifier/verify-artifact! (fixture))))))
