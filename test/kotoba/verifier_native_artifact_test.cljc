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
  by `amu compile --jvm-free`, and it is not trusted because it compiled:
  measured 2026-09-08, `amu extract-native` gave `:offset 0 :length 8` and
  `kexe_loader <bin> 0 0 aarch64 -` printed 42. Rebuild it the same way, and
  run it, if this repository's osaho pin moves the target profile again."
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

(defn- read-fixture [name]
  (guest-numbers
   (edn/read-string
    #?(:clj (slurp (io/resource (str "fixtures/" name)))
       :cljs (fs/readFileSync (path/join "resources" "fixtures" name) "utf8")))))

(defn- fixture [] (read-fixture "aarch64-demo.kexe"))

(defn- closure-fixture []
  ;; `examples/held-operations.kotoba` compiled to aarch64-macos. What makes
  ;; it a different fixture from the one above, rather than a bigger one, is
  ;; that its functions carry `:closure-param-indexes` and
  ;; `:i64-pair-chain-param-indexes` -- artifact fields this verifier uses as
  ;; HOST indexes and set members, which `aarch64-demo` has none of.
  ;; Measured on the loader: `held-score` answers 54.
  (read-fixture "aarch64-closure-params.kexe"))

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

(defn- outcome
  "Verification reduced to what this file cares about: did the verifier reach
  an admission DECISION, or did it die on the way to one?

  `reject!` throws `ex-info` with `:phase :verify`. A host type error throws
  something with no ex-data at all, which is a different event entirely: the
  CLI turns the first into `:kotoba/verification-failed` and the second into
  `:kotoba/internal-error`, sending the reader to look at the compiler
  instead of at the artifact."
  [artifact]
  (try {:decision :admitted :value (verifier/verify-artifact! artifact)}
       (catch #?(:clj Throwable :cljs :default) e
         (if-let [phase (:phase (ex-data e))]
           {:decision :refused :phase phase :message (ex-message e)}
           {:decision :host-error :message (ex-message e)}))))

(deftest a-param-index-out-of-an-artifact-is-usable-as-an-index
  ;; The seventh site of the same class, and the first that was not a refusal
  ;; at all: on cljs the verifier threw a JavaScript TypeError ("Index
  ;; argument to nth must be a number") because `guest-integer?` admits a
  ;; bigint and `nth` does not take one. `set` and `distinct` throw for a
  ;; different reason on the same value (they hash it), so the two index
  ;; predicates had three ways to die and no way to decide.
  ;;
  ;; The assertion is deliberately about REACHING a decision rather than
  ;; about which decision. This fixture is in fact refused here, for an
  ;; unrelated and recorded reason -- this repository's kotoba-native pin is
  ;; older than the amu that built it, so the re-emitted export table differs
  ;; (see the pin's comment in deps.edn). Asserting `map?` would tie this
  ;; test to that pin and hide what it is actually measuring.
  ;;
  ;; Discriminates on cljs only; on the JVM a guest index has always been a
  ;; host index. It lives in the `.cljc` file anyway, because the point of
  ;; the pair is that both hosts run the same assertion.
  (let [{:keys [decision message]} (outcome (closure-fixture))]
    (is (not= :host-error decision)
        (str "verification died instead of deciding: " message))))

(deftest a-param-index-is-still-checked
  (testing "the assertion above did not just stop looking at the indexes"
    ;; One index moved past the parameter list. If `guest-index` had been
    ;; spelled as "skip the check when the value is a bigint" this would come
    ;; back admitted, and if the fixture stopped carrying indexes at all the
    ;; first assertion would say so rather than passing vacuously.
    (let [artifact (closure-fixture)
          functions (get-in artifact [:program :functions])
          index (first (keep-indexed
                        (fn [i f] (when (contains? f :closure-param-indexes) i))
                        functions))]
      (is (some? index)
          "the closure fixture no longer carries :closure-param-indexes")
      (is (= :refused
             (:decision (outcome (assoc-in artifact
                                           [:program :functions index
                                            :closure-param-indexes]
                                           [#?(:clj 99 :cljs (js/BigInt 99))]))))))))

(deftest a-real-native-artifact-verifies-on-this-host
  ;; Both hosts, and the assertion is the same one on each: the WHOLE
  ;; artifact, not a chosen subset of gates.
  ;;
  ;; This was `#?(:cljs ...)` only, above a comment explaining that the JVM
  ;; refused the same fixture with "native target profile does not match
  ;; target identity" and calling that a fixture-vintage fact nothing here
  ;; could fix. The diagnosis was right and the conclusion was wrong: this
  ;; verifier RE-DERIVES the target profile from its own `kotoba.kir.target`,
  ;; so the skew was between this repository's osaho pin and the compiler's,
  ;; not inside the artifact. Advancing the pin and rebuilding the fixture
  ;; ended it. The cljs half had been passing for the shallower reason that
  ;; its pin happened to agree.
  ;;
  ;; Leaving it as a documented failure was the expensive part: a suite with
  ;; a permanent red in it stops being read, and this one carries the only
  ;; native artifact either host verifies.
  (is (map? (verifier/verify-artifact! (fixture)))))
