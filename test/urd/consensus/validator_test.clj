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

(defn await-finalized
  "Block until every validator has finalized at least `n` heights, or the
  deadline passes. Returns true if all reached it.

  Replaces a fixed `(<!! (timeout 2000))`. The claim these tests make is that
  consensus is REACHED, not that it is reached inside a particular number of
  milliseconds -- and a fixed sleep makes the outcome depend on how loaded the
  machine is. Standalone these passed; run after `kabel-network-test` in the
  full suite, on a busy JVM, two seconds was not enough and they reported a
  consensus failure that had not happened. Same defect as `runtime-test`'s
  flake, same fix."
  [validators n deadline-ms]
  (let [deadline (+ (System/currentTimeMillis) deadline-ms)]
    (loop []
      (cond
        (every? #(>= (count (validator/get-finalized %)) n) validators) true
        (> (System/currentTimeMillis) deadline) false
        :else (do (<!! (timeout 100)) (recur))))))
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

     ;; Teardown must be unconditional. It used to be the last form of this
     ;; body, so anything that threw first -- a `<??`, a helper -- skipped it
     ;; and left three validators running with live peers, timers and sockets
     ;; for the rest of the JVM. One run spent nine minutes with a leaked node
     ;; republishing `:want-proposal` into a closed channel on this very port,
     ;; and the suite never reported a result at all.
      (try
      ;; Start consensus on all validators simultaneously
        (helper/start-all-consensus! network)

      ;; Wait for initial consensus round
        (await-finalized validators 1 30000)

      ;; Verify all validators have finalized at least one height
        (doseq [v validators]
          (let [finalized (validator/get-finalized v)
                finalized-count (count finalized)]
            (is (>= finalized-count 1)
                (str "Validator " (:peer-id v) " should finalize at least 1 height"))))

      ;; Wait for more rounds
        (await-finalized validators 3 30000)

      ;; Verify continued progress (at least 3 heights finalized)
        (doseq [v validators]
          (let [finalized (validator/get-finalized v)
                finalized-count (count finalized)]
            (is (>= finalized-count 3)
                (str "Validator " (:peer-id v) " should finalize at least 3 heights"))))

      ;; Verify all validators AGREE on the heights they share.
      ;;
      ;; Not that they hold the SAME SET, which is what this asserted and is
      ;; not a consensus property. The cluster is still running while the test
      ;; reads it, one validator at a time, so a node that finalizes one more
      ;; height between the first read and the last makes the sets differ --
      ;; observed as #{0 1 2} #{0 1 2} #{0 1 2 3}, which is a correct cluster
      ;; sampled at three instants. The assertion demanded a synchronous
      ;; snapshot of an asynchronous system and failed roughly one run in two.
      ;;
      ;; What consensus actually promises is that no two validators finalize
      ;; DIFFERENT values at the same height, and that each holds a contiguous
      ;; prefix. Both are checked below, and both are violated by a real
      ;; disagreement -- which the set-equality check would also have caught,
      ;; along with a great deal else.
        (let [all-finalized (helper/get-all-finalized network)]
          (doseq [{ida :validator-id fa :finalized} all-finalized
                  {idb :validator-id fb :finalized} all-finalized
                  :when (not= ida idb)
                  h (filter (set (keys fb)) (keys fa))]
            (is (= (get fa h) (get fb h))
                (str "validators " ida " and " idb
                     " finalized different values at height " h)))
          (doseq [{:keys [validator-id finalized]} all-finalized]
            (is (= (sort (keys finalized)) (range (count finalized)))
                (str "validator " validator-id
                     " holds a contiguous prefix from 0, not a set with holes"))))

      ;; Print summary
        (println "\n========== Test Summary ==========")
        (doseq [{:keys [validator-id finalized]} (helper/get-all-finalized network)]
          (println "Validator" validator-id ":"
                   (count finalized) "heights finalized"))
        (println "==================================\n")
        (finally
          (<?? S (helper/stop-network! network)))))))

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

      (try
      ;; Start consensus on all validators simultaneously
        (helper/start-all-consensus! network)

      ;; Wait for consensus rounds
        (await-finalized validators 2 30000)

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
        (finally
          (<?? S (helper/stop-network! network)))))))
