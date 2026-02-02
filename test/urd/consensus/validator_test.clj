(ns urd.consensus.validator-test
  "Integration tests for consensus validators using Kabel P2P network."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.core.async :refer [<!! timeout]]
            [superv.async :refer [S <?? go-try-]]
            [urd.consensus.validator :as validator]
            [urd.consensus.network-helper :as helper]))

;; ============================================================
;; Integration Tests
;; ============================================================

(deftest ^:integration three-validator-consensus-test
  (testing "Three validators can reach consensus via Kabel"
    (let [;; Create proposal counter per validator
          proposal-counters (atom {})

          ;; Start network of 3 validators
          network (<?? S (helper/start-kabel-network! 3
                                                      {:on-propose (fn [vid]
                                                                     (helper/create-test-proposal
                                                                      vid
                                                                      (swap! proposal-counters update vid (fnil inc 0))))}))
          validators (:validators network)]

      ;; Start consensus on all validators simultaneously
      (helper/start-all-consensus! network)

      ;; Wait for initial consensus round
      (<!! (timeout 2000))

      ;; Verify all validators have finalized at least one height
      (doseq [v validators]
        (let [finalized (validator/get-finalized v)
              finalized-count (count finalized)]
          (is (>= finalized-count 1)
              (str "Validator " (:peer-id v) " should finalize at least 1 height"))))

      ;; Wait for more rounds
      (<!! (timeout 5000))

      ;; Verify continued progress (at least 3 heights finalized)
      (doseq [v validators]
        (let [finalized (validator/get-finalized v)
              finalized-count (count finalized)]
          (is (>= finalized-count 3)
              (str "Validator " (:peer-id v) " should finalize at least 3 heights"))))

      ;; Verify all validators finalized same heights
      (let [all-finalized (helper/get-all-finalized network)
            heights-sets (map (fn [{:keys [finalized]}]
                                (set (keys finalized)))
                              all-finalized)
            first-heights (first heights-sets)]
        (is (apply = heights-sets)
            "All validators should finalize same heights"))

      ;; Print summary
      (println "\n========== Test Summary ==========")
      (doseq [{:keys [validator-id finalized]} (helper/get-all-finalized network)]
        (println "Validator" validator-id ":"
                 (count finalized) "heights finalized"))
      (println "==================================\n")

      ;; Cleanup
      (<?? S (helper/stop-network! network)))))

(deftest ^:integration five-validator-consensus-test
  (testing "Five validators can reach consensus via Kabel"
    (let [;; Create proposal counter per validator
          proposal-counters (atom {})

          ;; Start network of 5 validators
          network (<?? S (helper/start-kabel-network! 5
                                                      {:base-port 47310
                                                       :on-propose (fn [vid]
                                                                     (helper/create-test-proposal
                                                                      vid
                                                                      (swap! proposal-counters update vid (fnil inc 0))))}))
          validators (:validators network)]

      ;; Start consensus on all validators simultaneously
      (helper/start-all-consensus! network)

      ;; Wait for consensus rounds
      (<!! (timeout 5000))

      ;; Verify all validators finalized
      (doseq [v validators]
        (let [finalized (validator/get-finalized v)
              finalized-count (count finalized)]
          (is (>= finalized-count 2)
              (str "Validator " (:peer-id v) " should finalize at least 2 heights"))))

      ;; Print summary
      (println "\n========== Five Validator Test Summary ==========")
      (doseq [{:keys [validator-id finalized]} (helper/get-all-finalized network)]
        (println "Validator" validator-id ":"
                 (count finalized) "heights finalized"))
      (println "==================================================\n")

      ;; Cleanup
      (<?? S (helper/stop-network! network)))))
