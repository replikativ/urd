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

    NAKAMOTO {:tip \"00488c18391b0c201c7ec97ee4d99333252eb3c800b3503a3d081396c6813490\",
              :height 6,
              :work \"00000000000000000000000000000000000000000000000000000000000000d4\",
              :bits [545259519 538968063 538968063 537395199 537395199 537001983],
              :nonces [0 10 3 76 2 77]}"
  (:require [clojure.test :as t]
            [urd.consensus.portability-test]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.algorithms.nakamoto :as nk]
            [urd.consensus.bignat :as bn]
            [urd.consensus.node :as node]
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

(defn nakamoto-fingerprint
  "A short mined chain reduced to a comparable value.

  Every quantity here is computed by code that a double cannot represent: the
  block ids are double-SHA256 over an 80-byte encoding, the work is a 256-bit
  sum, and the `bits` come out of a difficulty retarget whose arithmetic runs
  through the compact codec. The nonces are the toy miner's, so they also pin
  the proof-of-work COMPARISON -- a node that accepted a different first nonce
  would have a different notion of which hashes meet a target.

  Trivial difficulty on purpose: this is a portability check, not mining."
  []
  (let [genesis {:version 1 :prev nk/zero-hash :merkle-root nk/zero-hash
                 :time 1600000000 :bits 0x207fffff :nonce 0}
        p {:pow-limit-bits 0x207fffff :blocks-per-retarget 2 :target-timespan 1200}
        st0 (:state (node/init (nk/create) {:peer-id :fp :validators [:fp]
                                            :params p :genesis genesis
                                            :now 2000000000}))
        [st ids] (loop [st st0, i 0, ids []]
                   (if (= i 6)
                     [st ids]
                     (let [tip (:tip st)
                           tpl (nk/template st
                                            {:time (inc (get-in st [:blocks tip :header :time]))
                                             :merkle-root (str (apply str (repeat 63 "0")) i)})
                           h (nk/mine tpl 1000000)]
                       (recur (:state (nk/process-header st h nil))
                              (inc i) (conj ids (nk/header-id h))))))]
    {:tip (:tip st)
     :height (nk/height st (:tip st))
     :work (bn/to-hex (nk/tip-work st) 32)
     :bits (mapv #(get-in st [:blocks % :header :bits]) ids)
     :nonces (mapv #(get-in st [:blocks % :header :nonce]) ids)}))

(defn -main [& _]
  (t/run-tests 'urd.consensus.portability-test)
  (println "FINGERPRINT" (pr-str (fingerprint)))
  (println "NAKAMOTO" (pr-str (nakamoto-fingerprint))))

(set! *main-cli-fn* -main)
