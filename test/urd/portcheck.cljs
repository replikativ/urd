(ns urd.portcheck
  "ClojureScript entry point for the portability check.

  The JVM test runner cannot prove that a `.cljc` algorithm behaves the same in
  a browser, and the difference is not hypothetical -- `urd.consensus.rng`
  produced different random sequences under ClojureScript for as long as it
  existed, because `bit-and` there yields a SIGNED 32-bit integer. Every test
  that could have caught it was `.clj`.

  So this runs `urd.consensus.portability-test` under Node, and then prints a
  FINGERPRINT of a 400-tick, five-node Raft simulation. The fingerprint must be
  character-for-character identical to the one the JVM prints for the same
  scenario. Because every source of variation in the simulator -- message delay,
  drop, duplication, election timeout -- is drawn from the seed, any divergence
  at all means some arithmetic differs between the platforms.

  Build and run:

    clojure -M:test -e \"(require '[cljs.build.api :as b]) \\
      (b/build (b/inputs \\\"test/urd/portcheck.cljs\\\") \\
               {:output-to \\\"target/portcheck.js\\\" \\
                :output-dir \\\"target/portcheck\\\" \\
                :optimizations :simple :target :nodejs \\
                :main 'urd.portcheck})\"
    node target/portcheck.js

  Expected, and verified identical on both platforms:

    FINGERPRINT {:roles [:follower :follower :follower :follower :leader],
                 :terms [1 1 1 1 1],
                 :commits [53 53 53 53 54],
                 :committed-counts [53 53 53 53 54]}

    TENDERMINT-FINGERPRINT
      {:heights [17 17 17 17],
       :rounds [0 0 0 0],
       :decided [[:n1 0 0] [:n3 1 1] [:n3 2 0] [:n4 3 0] [:n1 4 0] [:n2 5 0]
                 [:n3 6 0] [:n4 7 0] [:n1 8 0] [:n2 9 0] [:n3 10 0] [:n4 11 0]
                 [:n1 12 0] [:n2 13 0] [:n3 14 0] [:n4 15 0] [:n1 16 0]]}

  The Tendermint line is the stronger of the two, because the round-1 decision
  at height 1 means the run actually took a timeout path: it pins the timeout
  schedule and the proposer rotation, not just the happy case."
  (:require [clojure.test :as t]
            [urd.consensus.portability-test]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.tendermint :as tm]
            [urd.consensus.sim :as sim]))

(def peers [:n1 :n2 :n3 :n4 :n5])

(defn fingerprint
  "A whole simulation reduced to a comparable value."
  []
  (let [s (sim/run (sim/make {:seed 42
                              :nodes (zipmap peers (repeat (raft/make)))
                              :node-config (zipmap peers (repeat {:election-timeout 10
                                                                  :heartbeat-timeout 3
                                                                  :propose-interval 7}))
                              :config {:min-delay 1 :max-delay 3 :persist-latency 2
                                       :value-fn (fn [sm p _] {:v (:tick sm) :by p})}})
                   400)]
    {:roles (mapv #(:role (sim/node-state s %)) peers)
     :terms (mapv #(:term (sim/node-state s %)) peers)
     :commits (mapv #(:commit (sim/node-state s %)) peers)
     :committed-counts (mapv #(count (sim/committed s %)) peers)}))

(def tm-peers [:n1 :n2 :n3 :n4])

(defn tendermint-fingerprint
  "A four-node Tendermint run under 20% message loss, reduced to a value.

  Chosen because it exercises every source of platform-dependent arithmetic in
  the port at once: proposer priorities (three different integer divisions),
  quorum thresholds, the logical timeout schedule, and the RNG-driven drop and
  delay decisions that decide which round each height lands in."
  []
  (let [s (sim/run (sim/make {:seed 42
                              :nodes (zipmap tm-peers (repeat (tm/make)))
                              :node-config (zipmap tm-peers
                                                   (repeat {:timeout-propose 20
                                                            :timeout-prevote 15
                                                            :timeout-precommit 15
                                                            :timeout-delta 5}))
                              :config {:drop-rate 0.2
                                       :value-fn (fn [_ p ctx]
                                                   {:id [p (:height ctx) (:round ctx)]})}})
                   300)]
    {:heights (mapv #(:height (sim/node-state s %)) tm-peers)
     :rounds (mapv #(:round (sim/node-state s %)) tm-peers)
     :decided (mapv :id (sim/committed s :n1))}))

(defn -main [& _]
  (t/run-tests 'urd.consensus.portability-test)
  (println "FINGERPRINT" (pr-str (fingerprint)))
  (println "TENDERMINT-FINGERPRINT" (pr-str (tendermint-fingerprint))))

(set! *main-cli-fn* -main)
