(ns kotoba.verifier-signing-parity-test
  "The same key, the same value, the same signature -- on both hosts.

  `kotoba.verifier.signing` was `.clj` until 2026-09-08, which is why
  `amu keygen`, `sign`, `verify` and `run` all answered
  `REFUSED: clojure was invoked` on a PATH with no java. Porting it to
  `.cljc` is only safe if the two hosts agree on bytes, so this pins that
  rather than asserting it in a docstring.

  The vector below was produced on NODE. Ed25519 is deterministic, so a JVM
  signing the same value with the same key must produce the identical base64
  -- and the JVM verifying the Node signature must accept it. Both are
  asserted, and this file is in BOTH suites, so each host checks the other's
  work.

  A roundtrip test alone would not do this. A host can be perfectly
  self-consistent and still disagree with the other one about DER, and a
  suite that only ever signs and verifies within one process cannot see it."
  (:require [clojure.test :as t :refer [deftest is testing]]
            [kotoba.verifier.signing :as signing]))

(def ^:private node-key
  {:format :kotoba.signing-key/v1
   :algorithm :ed25519
   :signer "87cb69195df314877e6c22b7c19a62bc0a6d9a096efd2ae9130b35df284a8d70"
   :public-key "MCowBQYDK2VwAyEAdHoBTPDuziogTLMZH/Z8WiWxTkszki6oHX7AQ+yNDWA="
   :private-key "MC4CAQAwBQYDK2VwBCIEIPXGcXwyFS07pQ83ITdqXx3r2bsuzoyRW9ObQDGyX/AH"})

(def ^:private node-value {:kotoba "parity" :n 7})
(def ^:private node-signature "qFiA289rBIiJ7K74TiEbqn2/1ep8Z0uT8VZPY9O4mbTU+9Ul+ZlezAP3k8h57+U6pqpAukX8kiAxeRTn5xhHAw==")

(deftest a-key-generated-on-the-other-host-is-valid-here
  (is (signing/valid-key? node-key))
  (is (= (:signer node-key) (signing/signer-id (:public-key node-key)))))

(deftest a-signature-made-on-the-other-host-verifies-here
  (is (signing/verify-value (:public-key node-key) node-value node-signature)))

(deftest signing-the-same-value-here-produces-the-same-bytes
  ;; Ed25519 is deterministic. If this fails the two hosts disagree about the
  ;; canonical bytes or the key encoding, and the signature format has forked.
  (is (= node-signature (signing/sign-value node-key node-value))))

(deftest a-tampered-value-is-refused
  (testing "the check above is not accepting everything"
    (is (false? (signing/verify-value (:public-key node-key)
                                      (assoc node-value :n 8)
                                      node-signature)))))

(deftest a-locally-generated-key-round-trips
  (let [k (signing/generate-keypair)
        v {:local "roundtrip"}]
    (is (signing/valid-key? k))
    (is (signing/verify-value (:public-key k) v (signing/sign-value k v)))))
