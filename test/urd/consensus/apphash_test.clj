(ns urd.consensus.apphash-test
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.apphash :as ah]))

(deftest a-value-carries-an-opaque-digest
  (testing "urd never computes one and never inspects one -- it is `=` on
            whatever the application produced"
    (is (= {:id 1 :app-hash "deadbeef"} (ah/attach {:id 1} "deadbeef")))
    (is (= {:id 1 :app-hash [:any :edn 42]} (ah/attach {:id 1} [:any :edn 42]))
        "not a string, not a hash -- whatever the application chose")
    (is (= {:id 1} (ah/attach {:id 1} nil))
        "and nothing at all before the application has applied anything, rather
         than a claim about an empty state")))

(deftest an-absent-digest-is-refused-by-default
  (testing "SECURITY, and the whole reason this is not a one-line predicate.

           The natural reading of a missing `:app-hash` is `this value makes no
           claim, so there is nothing to check`. Under that reading an attacker
           proposing a value simply OMITS the field, and every proposal it makes
           is exempt from exactly the check that would catch it. The bypass costs
           nothing and needs no key material.

           So absence is refused unless leniency is asked for by name -- the same
           rule `urd.consensus.auth/authenticator` follows, and for the same
           reason: a permissive default is how a check that is described but
           never performed survives review."
    (let [check (ah/checker (constantly "ours"))]
      (is (true? (check {:id 1 :app-hash "ours"})) "agreement passes")
      (is (false? (check {:id 1 :app-hash "theirs"})) "disagreement is refused")
      (is (false? (check {:id 1}))
          "and so is silence, which is the attack")))

  (testing "leniency exists, has to be typed, and is scoped"
    (let [lenient (ah/checker (constantly "ours") {:require? false})]
      (is (true? (lenient {:id 1})) "a value with no claim is tolerated")
      (is (false? (lenient {:id 1 :app-hash "theirs"}))
          "but a value that makes a WRONG claim is still refused -- leniency is
           about proposers that do not yet attach a digest, not about ignoring
           the ones that do"))))

(deftest genesis-has-nothing-to-disagree-with
  (testing "before the application has applied anything it has no state, so
            there is no digest to compare against. Refusing here would stop the
            FIRST value from ever being decided, which is a deadlock produced by
            a safety check."
    (let [check (ah/checker (constantly nil))]
      (is (true? (check {:id 1})))
      (is (true? (check {:id 1 :app-hash "anything"}))))))

(deftest the-current-digest-is-read-at-call-time
  (testing "`current-fn` is called per check, not captured once. The digest
            changes as values are applied, and a checker holding the digest from
            when it was built would reject every value after the first."
    (let [state (atom "h0")
          check (ah/checker (fn [] @state))]
      (is (true? (check {:app-hash "h0"})))
      (reset! state "h1")
      (is (false? (check {:app-hash "h0"})) "the old digest is now stale")
      (is (true? (check {:app-hash "h1"}))))))

(deftest a-decided-value-that-disagrees-reports-rather-than-votes
  (testing "`checker` and `verify!` answer different questions at different
            times, and conflating them loses the more serious one.

           `checker` runs BEFORE voting: its answer is `do not vote for this`,
           and a refused proposal simply is not adopted. `verify!` runs on a
           value a quorum has ALREADY decided -- so a mismatch does not mean the
           proposal is bad, it means WE diverged from the network. Voting
           differently cannot fix that."
    (let [seen (atom nil)]
      (is (true? (ah/verify! {:app-hash "same"} "same" #(reset! seen %))))
      (is (nil? @seen) "agreement reports nothing")

      (is (false? (ah/verify! {:app-hash "theirs"} "ours" #(reset! seen %))))
      (is (= {:claimed "theirs" :ours "ours" :value {:app-hash "theirs"}} @seen)
          "and a mismatch hands over both sides, so the application can say
           which state it is holding when it halts"))))
