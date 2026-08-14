(ns urd.consensus.algorithms.scp-portability-test
  "SCP values that MUST be identical on Clojure and ClojureScript.

  Run under both by `clj -X:test` and `clj -M:cljs-test`. §15 of the design doc
  records five checks that were green for the wrong reason, one of them `a
  portability claim with no JavaScript runtime to test it`; this file exists so
  that SCP does not become the sixth.

  SCP has more ways to diverge across platforms than any earlier algorithm,
  because two of its decisions are hash comparisons rather than counts:

    - `qset-hash` content-addresses quorum sets, and a node that computed a
      different hash from the same quorum set would fetch forever;
    - the nomination lottery decides which node leads a round, and if the JVM
      and the browser disagreed the two would nominate different values.

  Both run through `content-hash`, which alternates a djb2 step (exact on both
  platforms because its largest intermediate is about 1.4e11, inside 2^53) with
  an xorshift32 permutation (normalised to an unsigned 32-bit VALUE, not merely
  the right bits). The numbers below were taken on the JVM and verified under
  Node."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.algorithms.scp :as scp]
            [urd.consensus.sim :as sim]))

(def ^:private qset {:threshold 3 :validators [:a :b :c :d]})
(def ^:private peers [:a :b :c :d])

(deftest content-hash-agrees-across-platforms
  (testing "the draw is a NUMBER, not just a bit pattern

           `bit-and` in ClojureScript yields a signed 32-bit integer, so a
           priority could come out negative there and positive here -- and the
           lottery is a comparison, so the two platforms would elect different
           leaders from the same state."
    (is (every? #(and (>= % 0) (<= % 4294967295))
                (map scp/content-hash [":a" ":b" ":c" ":d" "[0,:genesis,true,1,:a]"])))
    (is (= [5381 2391404935 2718606413 245808509 565099159]
           (mapv scp/content-hash ["" "a" "abc" "a-fairly-long-node-identifier"
                                   "[0,:genesis,true,1,:d]"]))))
  (testing "and it avalanches: four peer ids differing in one character must not
           produce four nearly-equal priorities, or the lottery is rigged"
    (let [hs (mapv #(scp/content-hash (str "[" % ",0,:genesis,true,1]"))
                   [":a" ":b" ":c" ":d"])]
      (is (apply distinct? hs))
      (is (> (- (apply max hs) (apply min hs)) 1000000000)))))

(deftest qset-hash-agrees-across-platforms
  (testing "content addressing has to be identical everywhere, or a browser
           node and a server node fetch each other's quorum sets forever"
    (is (= 4261208957 (scp/qset-hash qset)))
    (is (= (scp/qset-hash qset)
           (scp/qset-hash {:validators [:d :c :b :a] :threshold 3}))
        "and independent of the order the validators are written in")
    (is (= 3205240440
           (scp/qset-hash {:threshold 2
                           :validators [:a]
                           :inner-sets [{:threshold 2 :validators [:b :c :d]}
                                        {:threshold 2 :validators [:e :f :g]}]})))))

(deftest quorum-predicates-agree-across-platforms
  (is (= [true false true false]
         [(scp/quorum-slice? qset #{:a :b :c})
          (scp/quorum-slice? qset #{:a :b})
          (scp/v-blocking? qset #{:a :b})
          (scp/v-blocking? qset #{:a})]))
  (is (= [true :unknown false]
         [(scp/quorum-tri qset #{:a :b :c} (constantly qset))
          (scp/quorum-tri qset #{:a :b :c} #(when (#{:a :b} %) qset))
          (scp/quorum-tri qset #{:a :b} (constantly qset))])))

(defn- fingerprint
  "A compact, order-stable summary of a whole SCP run.

  Deliberately not just \"did it agree\": message delays, drop decisions, the
  leader lottery, the ballot counters reached and the number of rule
  applications all feed into it, so a divergence anywhere shows up here."
  [seed drop-rate ticks]
  (let [s (sim/run (sim/make {:seed seed
                              :nodes (zipmap peers (repeat (scp/make)))
                              :node-config (into {} (map (fn [n]
                                                           [n {:qset qset
                                                               :qsets (zipmap peers (repeat qset))
                                                               :value n}]))
                                                 peers)
                              :config {:drop-rate drop-rate}})
                   ticks)]
    (mapv (fn [p]
            (let [st (sim/node-state s p)]
              [p (scp/phase st)
               (scp/externalized st)
               (:counter (first (scp/ballot-state st)))
               (vec (sort (map str (scp/candidates st))))
               (scp/rule-passes st)
               (vec (sim/committed s p))]))
          peers)))

(deftest simulation-fingerprint-agrees-across-platforms
  (testing "a clean run"
    (is (= [[:a :externalize :a 3 [":a"] 10 [:a]]
            [:b :externalize :a 3 [":a"] 11 [:a]]
            [:c :externalize :a 3 [":a"] 11 [:a]]
            [:d :externalize :a 3 [":a"] 11 [:a]]]
           (fingerprint 12345 0.0 60))))
  (testing "and a lossy one, where the retransmission timer is what saves it"
    (is (= [[:a :externalize :a 1 [":a"] 8 [:a]]
            [:b :externalize :a 2 [":a"] 9 [:a]]
            [:c :externalize :a 1 [":a"] 9 [:a]]
            [:d :externalize :a 1 [":a"] 9 [:a]]]
           (fingerprint 7 0.3 200)))))
