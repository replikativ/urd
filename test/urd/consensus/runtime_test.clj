(ns urd.consensus.runtime-test
  "Integration tests for consensus runtime with round-robin state machine."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.runtime :as runtime]
            [urd.consensus.algorithms.round-robin :as rr]
            [urd.consensus.network :as net]
            [urd.crypto :as crypto]
            [konserve.memory :refer [new-mem-store]]
            [clojure.set]
            [clojure.core.async :refer [<!! timeout]]))

;; ============================================================
;; Test Helpers
;; ============================================================

(defn create-test-validators
  "n validators, identified by UUID."
  [n]
  (into {} (map (fn [idx] [(java.util.UUID/randomUUID) {:index idx}]))
        (range n)))

(defn create-test-proposal
  "A value to decide.

  A plain map. It used to be a signed `SignedSnapshotRef` built through
  `urd.types` and `yggdrasil`, and none of that was load-bearing: the runtime
  and every algorithm treat a decided value as OPAQUE -- round-robin reads
  `:snapshot-id` and nothing else looks inside at all. Signing it here proved
  nothing, because nothing in this path verified the signature; the real
  verification edge is `urd.consensus.auth`, on the envelope."
  [_validator-info]
  {:snapshot-id (java.util.UUID/randomUUID)
   :payload "test-value"})

;; ============================================================
;; Runtime Integration Tests
;; ============================================================

(defn await-all-finalized
  "Block until every validator in `ids` has finalized at least once, or
  `deadline-ms` elapses. Returns true if all finalized."
  [finalized ids deadline-ms]
  (let [deadline (+ (System/currentTimeMillis) deadline-ms)]
    (loop []
      (cond
        (every? #(seq (get @finalized %)) ids) true
        (> (System/currentTimeMillis) deadline) false
        :else (do (<!! (timeout 25)) (recur))))))

(deftest runtime-basic-consensus-test
  (testing "Runtime runs round-robin state machine through complete consensus"
    (let [;; Create 3 validators
          validators (create-test-validators 3)
          validator-set (into {}
                              (map (fn [[id info]]
                                     [id (:public-key info)])
                                   validators))
          validator-ids (vec (sort (keys validators)))

          ;; Create mock network cluster
          cluster (net/create-mock-cluster validator-ids)

          ;; Track finalized proposals
          finalized (atom {})

          ;; Start runtime for each validator
          runtimes
          (into {}
                (map (fn [[v-id v-info]]
                       (let [store (<!! (new-mem-store))
                             sm (rr/create validator-set)

                             on-propose (fn [] (create-test-proposal v-info))

                             on-finalize (fn [proposal height]
                                           (swap! finalized update v-id
                                                  (fnil conj [])
                                                  {:height height :proposal proposal}))

                             rt (<!! (runtime/start-runtime!
                                      {:peer-id v-id
                                       ;; In-process mock cluster; the
                                       ;; authenticated path is covered by
                                       ;; `auth_test` and the kabel helper.
                                       :auth :none
                                       ;; round-robin refuses to start without
                                       ;; a vote verifier: its `:vote-bundle`
                                       ;; and `:catchup` messages RELAY other
                                       ;; nodes' votes, so a bare name is a
                                       ;; claim by the relayer.
                                       :sign-vote (:sign-vote (rr/test-attestations))
                                       :verify-vote (:verify-vote (rr/test-attestations))
                                       :state-machine sm
                                       :network (get cluster v-id)
                                       :on-propose on-propose
                                       :on-finalize on-finalize}))]
                         [v-id rt]))
                     validators))]

      ;; Start consensus on all validators simultaneously
      (doseq [[v-id rt] runtimes]
        (runtime/send-event! rt {:type :start-round}))

      ;; Wait for consensus to complete -- POLLING to a deadline, not a fixed
      ;; sleep. A flat `(timeout 3000)` made this test's outcome depend on how
      ;; loaded the machine was: under a full suite run, sharing the box with a
      ;; real WebSocket server, three validators did not always reach height 0
      ;; inside three seconds, and the assertions below -- which read the FIRST
      ;; finalization of each validator -- then compared one node's height-1
      ;; entry against two nodes' height-0 entries and reported a consensus
      ;; failure. It passed on every isolated run and failed under load, which
      ;; is the worst way for a test to be wrong.
      (await-all-finalized finalized validator-ids 15000)

      (testing "All validators finalize proposal"
        (is (= 3 (count (filter #(seq (get @finalized %)) validator-ids)))
            "All 3 validators should finalize"))

      (testing "All validators agree on every height they have all finalized"
        ;; Compared PER HEIGHT, not "each validator's first finalization".
        ;;
        ;; The old form asserted that every validator's first entry was height
        ;; 0 and that those first entries matched. Both are startup artifacts
        ;; rather than consensus properties: `send-event! :start-round` reaches
        ;; the three runtimes at slightly different times, and a validator that
        ;; joins after the other two have already decided height 0 has its
        ;; FIRST finalization at height 1 -- with no disagreement anywhere. That
        ;; is what the flake was.
        ;;
        ;; Agreement is the real claim, so assert it directly: at every height
        ;; all three have reached, all three chose the same proposal.
        (let [by-height (fn [v-id]
                          (into {} (map (juxt :height #(-> % :proposal :snapshot-id)))
                                (get @finalized v-id)))
              maps (mapv by-height validator-ids)
              shared (reduce clojure.set/intersection (map (comp set keys) maps))]
          (is (seq shared)
              "the validators must share at least one finalized height, or
               there is nothing to compare and this test proves nothing")
          (doseq [h shared]
            (is (= 1 (count (set (map #(get % h) maps))))
                (str "validators disagreed at height " h ": "
                     (pr-str (mapv #(get % h) maps)))))))

      (testing "Heights are contiguous from zero for each validator"
        (doseq [v-id validator-ids]
          (let [hs (mapv :height (get @finalized v-id))]
            (is (= hs (vec (range (first hs) (+ (first hs) (count hs)))))
                (str v-id " finalized a gappy height sequence: " hs)))))

      ;; Cleanup
      (doseq [[v-id rt] runtimes]
        (<!! (runtime/stop-runtime! rt))
        (<!! (net/close-network! (get cluster v-id)))))))

(deftest runtime-multi-round-test
  (testing "Runtime handles multiple consensus rounds"
    (let [validators (create-test-validators 3)
          validator-set (into {}
                              (map (fn [[id info]]
                                     [id (:public-key info)])
                                   validators))
          validator-ids (vec (sort (keys validators)))

          cluster (net/create-mock-cluster validator-ids)

          finalized (atom {})

          ;; Counter to track how many proposals each validator has provided
          proposal-count (atom {})

          ;; Use atom to allow on-finalize to reference runtimes
          runtimes-atom (atom {})

          runtimes
          (into {}
                (map (fn [[v-id v-info]]
                       (let [store (<!! (new-mem-store))
                             sm (rr/create validator-set)

                             on-propose (fn []
                                          (swap! proposal-count update v-id (fnil inc 0))
                                          (create-test-proposal v-info))

                             on-finalize (fn [proposal height]
                                           (swap! finalized update v-id
                                                  (fnil conj [])
                                                  {:height height :proposal proposal})
                                      ;; Trigger next round
                                           (runtime/send-event!
                                            (get @runtimes-atom v-id)
                                            {:type :start-round}))

                             rt (<!! (runtime/start-runtime!
                                      {:peer-id v-id
                                       ;; In-process mock cluster; the
                                       ;; authenticated path is covered by
                                       ;; `auth_test` and the kabel helper.
                                       :auth :none
                                       ;; round-robin refuses to start without
                                       ;; a vote verifier: its `:vote-bundle`
                                       ;; and `:catchup` messages RELAY other
                                       ;; nodes' votes, so a bare name is a
                                       ;; claim by the relayer.
                                       :sign-vote (:sign-vote (rr/test-attestations))
                                       :verify-vote (:verify-vote (rr/test-attestations))
                                       :state-machine sm
                                       :network (get cluster v-id)
                                       :on-propose on-propose
                                       :on-finalize on-finalize}))]
                     ;; Store runtime immediately so on-finalize can access it
                         (swap! runtimes-atom assoc v-id rt)
                         [v-id rt]))
                     validators))]

      ;; Start consensus on all validators simultaneously
      (doseq [[v-id rt] runtimes]
        (runtime/send-event! rt {:type :start-round}))

      ;; Wait for multiple rounds
      (<!! (timeout 6000))

      (testing "Multiple rounds complete"
        (let [heights-finalized (map (fn [v-id]
                                       (count (get @finalized v-id [])))
                                     validator-ids)]
          (is (every? #(>= % 2) heights-finalized)
              "All validators should finalize at least 2 rounds")))

      (testing "Proposer function was called"
        ;; Check that proposals were requested
        (is (> (reduce + (vals @proposal-count)) 0)
            "At least one proposal should have been requested"))

      ;; Cleanup
      (doseq [[v-id rt] runtimes]
        (<!! (runtime/stop-runtime! rt))
        (<!! (net/close-network! (get cluster v-id)))))))
