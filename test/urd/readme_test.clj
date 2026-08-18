(ns urd.readme-test
  "Every code block in README.md, executed.

  The README rotted badly enough to be worth a test: before this file it opened
  with six calls to `urd.crypto` functions that had been deleted months earlier
  -- the Quick Start did not run, and nothing noticed. Prose about code drifts
  from the code silently. A test does not.

  So the README quotes this file rather than the other way round. If you change
  an example there, change it here first and watch it pass.

  `.clj`, not `.cljc`: `<!!` and `attest/attestations` are both JVM-only, and
  the second deliberately so -- see `urd.consensus.attest`."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.core.async :refer [<!!]]
            [urd.consensus.attest :as attest]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.tendermint :as tm]))

(def peers [:a :b :c :d])

(defn cluster
  "Four Tendermint nodes in a deterministic simulator.

  `sim/make` needs only `:nodes` -- it derives the validator set from the node
  keys and runs each `init` immediately. `:value-fn` answers the
  `:request-value` effect; without one every node is handed `{:payload :none}`
  and decides nothing interesting."
  []
  (sim/make {:seed 7
             :nodes (zipmap peers (repeat (tm/make)))
             :config {:value-fn (fn [_sim peer ctx]
                                  {:id [:block peer (:height ctx)]})}}))

(deftest quick-start-commits-a-value
  (testing "the shortest path from nothing to a decided value: no network, no
            store, no keys, no auth"
    (let [s (sim/run (cluster) 200)]
      (is (sim/agreement? s))
      (is (pos? (count (sim/committed s :a))))
      (is (= {:id [:block :a 0]} (first (sim/committed s :a))))
      (is (apply = (vals (sim/all-committed s)))
          "and every node committed the same sequence"))))

(deftest quick-start-survives-a-minority-partition
  (testing "one of four is cut off, then healed. Agreement is a prefix
            property, so a lagging node is not a disagreeing one."
    (let [s (-> (cluster)
                (sim/run 40)
                (sim/partition-network [#{:a :b :c} #{:d}])
                (sim/run 60)
                sim/heal
                (sim/run 60))]
      (is (sim/agreement? s))
      (is (apply = (mapv #(:height (sim/node-state s %)) peers))
          "and the isolated node catches up"))))

(deftest quick-start-survives-a-crash-and-restart
  (testing "a crash loses buffered writes -- the simulator models that, and
            `urd.consensus.sim/crash` explains why not modelling it blinded
            every crash test that came before it"
    (let [s (-> (cluster)
                (sim/run 40)
                (sim/crash :b)
                (sim/run 40)
                (sim/restart :b)
                (sim/run 80))]
      (is (sim/agreement? s)))))

(deftest quick-start-certificate-verifies
  (testing "a commit certificate is checkable by someone who holds only the
            validator set -- and, per doc/interop, by someone who is not
            running Clojure at all"
    (let [chain "urd-testnet-1"
          payload [12 "block-12"]
          kps (into {} (for [v [:v1 :v2 :v3 :v4]]
                         [v (<!! (attest/generate-keypair))]))
          pks (into {} (for [[v kp] kps] [v (:public kp)]))
          votes (into {} (for [v [:v1 :v2 :v3]]
                           (let [{:keys [sign-vote]}
                                 (attest/attestations
                                  {:chain chain :peer-id v
                                   :private-key (:private (kps v))
                                   :public-keys pks})]
                             [v (sign-vote v payload)])))
          cert (attest/certificate {:chain chain :payload payload :votes votes})]
      (is (= {:valid? true :voters #{:v1 :v2 :v3} :quorum 3 :of 4}
             (<!! (attest/verify-certificate cert pks)))))))

(deftest round-robin-needs-a-snapshot-id
  (testing "the first-five-minutes trap, pinned so the README's warning cannot
            become false. A round-robin proposal is identified by
            `:snapshot-id`; a value without one has a nil id, every guard
            declines, and the cluster commits NOTHING -- with no error, no
            exception and no log line. Measured here rather than asserted."
    (let [rr (requiring-resolve 'urd.consensus.algorithms.round-robin/create)
          atts ((requiring-resolve 'urd.consensus.algorithms.round-robin/test-attestations))
          vs [:a :b :c]
          build (fn [value-fn]
                  (sim/make {:seed 3
                             :nodes (into {} (map (fn [v] [v (rr (zipmap vs (repeat nil)))])) vs)
                             :node-config (into {} (map (fn [v] [v (merge atts {:peer-id v
                                                                                :validators vs})])) vs)
                             :config {:value-fn value-fn}}))
          with-id (sim/run (build (fn [_ p ctx] {:snapshot-id [p (:height ctx)]
                                                 :payload :x}))
                           200)
          without (sim/run (build (fn [_ _ _] {:payload :x})) 200)]
      (is (pos? (count (sim/committed with-id :a))))
      (is (zero? (count (sim/committed without :a)))
          "no id, no commits, and nothing anywhere says why"))))
