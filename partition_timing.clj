(ns partition-timing
  (:require [clojure.core.async :refer [<!! timeout]]
            [urd.consensus.network :as net]
            [urd.consensus.round-robin :as rr]
            [urd.log :as log]
            [urd.crypto :as crypto]
            [yt.types :as yt]
            [konserve.memory :refer [new-mem-store]]))

(defn create-test-validators [n]
  (into {}
    (map (fn [_]
           (let [keypair (crypto/generate-keypair)
                 id (java.util.UUID/randomUUID)]
             [id {:private-key (:private-key keypair)
                  :public-key (:public-key keypair)}]))
         (range n))))

(defn create-test-proposal [validator-info]
  (let [snapshot (yt/->SnapshotRef
                   "test-system"
                   (java.util.UUID/randomUUID)
                   #{}
                   (yt/hlc-now)
                   "sha256:test-hash")]
    (crypto/sign-snapshot snapshot
                         (:private-key validator-info)
                         (:public-key validator-info))))

(defn -main [& args]
  (println "\n=== Starting Partition Experiment ===")
  (let [start-time (System/currentTimeMillis)
        validators (create-test-validators 5)
        validator-set (into {} (map (fn [[id info]] [id (:public-key info)]) validators))
        validator-ids (vec (sort (keys validators)))]

    (println "Validators created:" (count validators))
    (println "First validator (proposer at height 0):" (subs (str (first validator-ids)) 0 8))

    (let [cluster (net/create-mock-cluster validator-ids)
          partition-1 (set (take 3 validator-ids))
          partition-2 (set (drop 3 validator-ids))]

      (println "Partition 1 (majority):" (mapv #(subs (str %) 0 8) partition-1))
      (println "Partition 2 (minority):" (mapv #(subs (str %) 0 8) partition-2))
      (println "Proposer in partition 1?" (contains? partition-1 (first validator-ids)))

      (let [partitioned-cluster (net/simulate-network-partition cluster [partition-1 partition-2])
            finalized (atom {})
            finalize-times (atom {})

            consensus-states
            (into {}
              (map (fn [[v-id v-info]]
                     (let [store (<!! (new-mem-store))
                           consensus-log (log/create-consensus-log store validator-set)
                           on-propose (fn [] (create-test-proposal v-info))
                           on-finalize (fn [proposal height]
                                        (let [elapsed (- (System/currentTimeMillis) start-time)]
                                          (println (format "[%dms] Validator %s finalized height %d"
                                                          elapsed (subs (str v-id) 0 8) height))
                                          (swap! finalized update v-id (fnil conj []) {:height height :proposal proposal})
                                          (swap! finalize-times assoc v-id elapsed)))
                           state (rr/start-consensus!
                                   {:peer-id v-id
                                    :validator-set validator-set
                                    :consensus-log consensus-log
                                    :network (get partitioned-cluster v-id)
                                    :on-propose on-propose
                                    :on-finalize on-finalize
                                    :proposal-timeout-ms 1000
                                    :private-key (:private-key v-info)})]
                       [v-id state]))
                   validators))]

        (println "\nWaiting for finalization...")

        (loop [checks 0]
          (when (< checks 10)
            (<!! (timeout 500))
            (let [elapsed (- (System/currentTimeMillis) start-time)
                  majority-finalized (count (filter #(seq (get @finalized %)) partition-1))
                  minority-finalized (count (filter #(seq (get @finalized %)) partition-2))]
              (println (format "[%dms] Check %d: Majority=%d/3, Minority=%d/2"
                              elapsed (inc checks) majority-finalized minority-finalized))
              (when (< majority-finalized 3)
                (recur (inc checks))))))

        (println "\n=== Final Results ===")
        (println "Finalized by validator:")
        (doseq [v-id validator-ids]
          (let [heights (count (get @finalized v-id []))
                time (@finalize-times v-id)]
            (println (format "  %s: %d heights%s"
                            (subs (str v-id) 0 8) heights
                            (if time (str " (at " time "ms)") "")))))

        (let [majority-finalized (filter #(seq (get @finalized %)) partition-1)
              minority-finalized (filter #(seq (get @finalized %)) partition-2)]
          (println (format "\nMajority finalized: %d/3" (count majority-finalized)))
          (println (format "Minority finalized: %d/2" (count minority-finalized))))

        (doseq [[v-id state] consensus-states]
          (<!! (rr/stop-consensus! state))
          (<!! (net/close-network! (get partitioned-cluster v-id))))

        (println "\n=== Experiment Complete ===")
        (System/exit 0)))))

(-main)
