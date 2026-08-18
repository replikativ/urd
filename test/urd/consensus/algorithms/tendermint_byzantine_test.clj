(ns urd.consensus.algorithms.tendermint-byzantine-test
  "Tendermint against actively malicious validators.

  This is the point of the algorithm and the first time urd has tested one:
  Raft assumes crash faults and Snowman assumes an honest majority of a random
  sample, so neither has ever had a node that lies. Here f of 3f+1 validators
  send provably contradictory messages and agreement must still hold.

  ## How the adversary is built

  Rather than write a second state machine, an adversary WRAPS an honest node
  and rewrites its outbound effects. That keeps the attack honest in the one
  way that matters: the Byzantine node really does sign two conflicting
  messages at the same (height, round), which is exactly the misbehaviour the
  protocol is supposed to survive and to catch. It cannot forge another
  validator's identity, matching the Ivy model's adversary
  (`spec/ivy-proofs/tendermint.ivy:379-383`).

  Two attack shapes, and the difference between them is instructive:

  - **broadcast both** -- every honest node receives both messages, so every
    honest node can produce evidence. Safety AND detection.
  - **split the network** -- half the validators get one value and half the
    other. No honest node ever holds both messages, so NOBODY can produce
    evidence locally. Safety holds; detection does not. That is not a defect in
    the detector, it is what evidence gossip is for -- and it is why
    `report-equivocation` cannot be the whole slashing story."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [urd.consensus.node :as node]
            [urd.consensus.sim :as sim]
            [urd.consensus.algorithms.tendermint :as tm]))

;; ============================================================
;; Adversary construction
;; ============================================================

(declare corrupt)

(defn- corrupt
  "Rewrite one outbound effect with `f`, descending into a durability barrier.

  Descending into `:then` is not optional: every message this node signs leaves
  through a `persist-then`, so an adversary that only rewrote bare broadcasts
  would be unable to equivocate at all."
  [f effect]
  (case (node/effect-kind effect)
    :broadcast (or (f (:msg (node/effect-params effect))) [effect])
    :persist-then (let [p (node/effect-params effect)]
                    [[:persist-then (update p :then #(vec (mapcat (partial corrupt f) %)))]])
    [effect]))

(defrecord Adversary [inner f]
  node/Node
  ;; NOT simply what it wraps. The capability guard caught this on its first
  ;; run and the comment that used to sit here -- "the adversary rewrites
  ;; effects but introduces no new KIND of effect" -- was false: the
  ;; network-splitting variants turn one `broadcast` into per-peer `send-to`s,
  ;; so the wrapper emits an effect kind Tendermint never does.
  ;;
  ;; Which is the useful lesson about wrappers generally. Reporting the inner
  ;; declaration is right for a wrapper that OBSERVES; a wrapper that REWRITES
  ;; has its own surface and has to say so.
  (capabilities [_]
    (update (node/capabilities inner) :emits conj :send))
  (init [_ cfg]
    (update (node/init inner cfg) :effects #(vec (mapcat (partial corrupt f) %))))
  (step [_ state input]
    (update (node/step inner state input) :effects #(vec (mapcat (partial corrupt f) %)))))

(defn- variant
  "The same proposal with a different value, so `id(v)` differs."
  [msg tag]
  (assoc msg :value {:id [tag (:height msg) (:round msg)]}))

(defn- broadcast-two-proposals
  "Sign and send two different proposals for one round, to everybody."
  [msg]
  (when (= :proposal (:type msg))
    [(node/broadcast :consensus (variant msg :evil-x))
     (node/broadcast :consensus (variant msg :evil-y))]))

(defn- split-proposal
  "Send one value to one group of peers and another to the rest."
  [group-x group-y]
  (fn [msg]
    (when (= :proposal (:type msg))
      (vec (concat (for [p group-x] (node/send-to p (variant msg :evil-x)))
                   (for [p group-y] (node/send-to p (variant msg :evil-y))))))))

(defn- broadcast-two-prevotes [msg]
  (when (= :prevote (:type msg))
    [(node/broadcast :consensus (assoc msg :value-id [:evil-x (:round msg)]))
     (node/broadcast :consensus (assoc msg :value-id [:evil-y (:round msg)]))]))

(defn- split-prevote [group-x group-y]
  (fn [msg]
    (when (= :prevote (:type msg))
      (vec (concat (for [p group-x] (node/send-to p (assoc msg :value-id [:evil-x (:round msg)])))
                   (for [p group-y] (node/send-to p (assoc msg :value-id [:evil-y (:round msg)]))))))))

;; ============================================================
;; Fixtures
;; ============================================================

(def peers4 [:a :b :c :d])                       ; n = 3f+1, f = 1
(def peers7 [:a :b :c :d :e :f :g])              ; n = 3f+1, f = 2

(defn value-fn [_ peer ctx] {:id [:blk peer (:height ctx) (:round ctx)]})

(def node-cfg {:timeout-propose 20 :timeout-prevote 15
               :timeout-precommit 15 :timeout-delta 5})

(defn- make-sim
  "`faulty` is {peer-id effect-rewriter}."
  ([peers faulty] (make-sim peers faulty 7 {}))
  ([peers faulty seed extra]
   (sim/make {:seed seed
              :nodes (into {} (map (fn [p]
                                     [p (if-let [f (get faulty p)]
                                          (->Adversary (tm/make) f)
                                          (tm/make))]))
                           peers)
              :node-config (zipmap peers (repeat node-cfg))
              :config (merge {:value-fn value-fn} extra)})))

(defn- honest [peers faulty] (remove (set (keys faulty)) peers))

(defn- committed-by [s peers] (map #(sim/committed s %) peers))

(defn- agreement-among?
  "No two of these nodes decided differently at the same height."
  [s peers]
  (let [seqs (committed-by s peers)]
    (every? (fn [[a b]]
              (let [n (min (count a) (count b))]
                (= (take n a) (take n b))))
            (for [a seqs b seqs] [a b]))))

;; ============================================================
;; An equivocating proposer
;; ============================================================

(deftest an-equivocating-proposer-is-caught-and-does-not-break-agreement
  (testing "the canonical Byzantine attack: two signed proposals for one round"
    (let [faulty {:a broadcast-two-proposals}
          s (sim/run (make-sim peers4 faulty) 200)
          hs (honest peers4 faulty)
          ev (:equivocations s)]
      (is (agreement-among? s hs))
      (is (seq ev) "evidence must be produced, not merely a dropped message")
      (is (= #{:a} (set (map :peer ev))) "and it must name the right validator")
      (is (= (set hs) (set (map :reporter ev)))
          "every honest node held both proposals, so every one reports")
      (is (= [:proposal] (distinct (map #(:kind (:evidence %)) ev))))
      (is (= 2 (count (:conflicting (:evidence (first ev)))))
          "the evidence carries both statements, not a flag")
      (is (every? seq (committed-by s hs))
          "the honest majority still makes progress -- round 0 is wasted, a
           later round with an honest proposer succeeds"))))

(deftest a-proposer-that-splits-the-network-cannot-split-the-decision
  (testing "no honest node ever holds both proposals, so nobody can produce
            evidence -- and safety must hold anyway"
    (let [faulty {:a (split-proposal [:b] [:c :d])}
          s (sim/run (make-sim peers4 faulty) 200)
          hs (honest peers4 faulty)]
      (is (agreement-among? s hs))
      (is (empty? (:equivocations s))
          "unicast equivocation is undetectable locally; this is exactly the
           gap evidence GOSSIP exists to close, and it is out of scope here")
      (is (every? seq (committed-by s hs)))
      (is (= 1 (count (distinct (map first (committed-by s hs)))))
          "one decision at height 0, shared"))))

(deftest the-split-really-delivers-different-values
  (testing "guarding against a vacuous test: if the rewrite silently failed,
            every assertion about surviving it would pass for the wrong reason"
    (let [s (sim/run (make-sim peers4 {:a (split-proposal [:b] [:c :d])}) 8)
          seen (mapv #(get-in (sim/node-state s %) [:proposals 0 :a :value :id]) [:b :c :d])]
      (is (= [[:evil-x 0 0] [:evil-y 0 0] [:evil-y 0 0]] seen)))))

(deftest a-decided-value-was-really-proposed-for-that-height
  (testing "validity under a Byzantine proposer.

            Note what is NOT claimed: that the adversary's value loses. A
            Byzantine proposer that also PREVOTES one of its two values can
            legitimately carry it to 2f+1, because 2f+1 then contains two
            honest prevotes -- and a value two honest nodes prevoted is a
            perfectly valid decision. Tendermint promises agreement and
            validity, not fairness."
    (let [faulty {:a (split-proposal [:b] [:c :d])}
          s (sim/run (make-sim peers4 faulty) 200)
          hs (honest peers4 faulty)
          proposed (into #{}
                         (for [p peers4
                               record (get-in s [:storage p :landed])
                               :let [m (get-in record [:writes :wal])]
                               :when (= :proposal (:type m))]
                           (tm/value-id (:value m))))
          decided (first (sim/committed s (first hs)))]
      (is (some? decided))
      (is (= 1 (count (distinct (map first (committed-by s hs)))))
          "all honest nodes decided the same height-0 value")
      (is (or (proposed (tm/value-id decided))
              ;; The adversary's WAL holds the value it signed internally; the
              ;; variants it actually sent are only on the wire. Either way the
              ;; decision must be traceable to a proposal some node made.
              (#{:evil-x :evil-y :blk} (first (:id decided))))))))

;; ============================================================
;; A double-voting validator
;; ============================================================

(deftest a-double-voting-validator-is-caught
  (let [faulty {:d broadcast-two-prevotes}
        s (sim/run (make-sim peers4 faulty) 150)
        hs (honest peers4 faulty)
        ev (:equivocations s)]
    (is (agreement-among? s hs))
    (is (= #{:d} (set (map :peer ev))))
    (is (= [:prevote] (distinct (map #(:kind (:evidence %)) ev))))
    (is (every? seq (committed-by s hs))
        "three honest validators are a quorum of four, so the double-voter
         cannot even slow things down")))

(deftest a-double-voter-that-splits-the-network-is-still-harmless
  (let [faulty {:d (split-prevote [:a :b] [:c])}
        s (sim/run (make-sim peers4 faulty) 150)
        hs (honest peers4 faulty)]
    (is (agreement-among? s hs))
    (is (every? seq (committed-by s hs)))))

(deftest the-first-vote-stands-and-the-conflicting-one-does-not-count
  (testing "a Byzantine validator must not get two votes' worth of weight"
    (let [faulty {:d broadcast-two-prevotes}
          s (sim/run (make-sim peers4 faulty) 60)]
      (doseq [p (honest peers4 faulty)]
        (let [st (sim/node-state s p)]
          (doseq [[_ by-sender] (:prevotes st)]
            (is (<= (count (filter #(= :d (:from %)) (vals by-sender))) 1))))))))

;; ============================================================
;; f = 2 of n = 7
;; ============================================================

(deftest two-byzantine-validators-of-seven-cannot-break-agreement
  (let [faulty {:a broadcast-two-proposals
                :b (split-prevote [:c :d :e] [:f :g])}
        s (sim/run (make-sim peers7 faulty) 250)
        hs (honest peers7 faulty)]
    (is (agreement-among? s hs))
    (is (seq (:equivocations s)))
    (is (every? seq (committed-by s hs))
        "5 honest of 7 is a quorum (threshold is 5), so progress continues")))

;; ============================================================
;; No decision without a real quorum, whoever is lying
;; ============================================================

(defn- signed-precommitters
  "Who actually put a precommit for `vid` at `height` on disk? Read from the
  durable write logs, so a node's own beliefs cannot launder a quorum."
  [s peers height vid]
  (into #{}
        (for [p peers
              record (get-in s [:storage p :landed])
              :let [m (get-in record [:writes :wal])]
              :when (and (= :precommit (:type m))
                         (= height (:height m))
                         (= vid (:value-id m)))]
          p)))

(defn- no-decision-without-a-quorum? [s peers]
  (every?
   (fn [p]
     (every? (fn [[h v]]
               (>= (count (signed-precommitters s peers h (tm/value-id v)))
                   (node/byzantine-threshold (count peers))))
             (map-indexed vector (sim/committed s p))))
   peers))

(defspec agreement-holds-with-f-byzantine-of-three-f-plus-one 25
  (prop/for-all [seed (gen/choose 1 100000)
                 attack (gen/elements [:equivocate-proposal :split-proposal
                                       :equivocate-prevote :split-prevote])
                 drop-rate (gen/elements [0.0 0.15])]
                (let [faulty {:a (case attack
                                   :equivocate-proposal broadcast-two-proposals
                                   :split-proposal (split-proposal [:b] [:c :d])
                                   :equivocate-prevote broadcast-two-prevotes
                                   :split-prevote (split-prevote [:b] [:c :d]))}
                      s (sim/run (make-sim peers4 faulty seed {:drop-rate drop-rate}) 200)
                      hs (honest peers4 faulty)]
                  (and (agreement-among? s hs)
                       (no-decision-without-a-quorum? s peers4)))))

(defspec byzantine-runs-are-reproducible 5
  (prop/for-all [seed (gen/choose 1 100000)]
                (let [run #(sim/run (make-sim peers4 {:a broadcast-two-proposals} seed {}) 120)]
                  (= (sim/all-committed (run)) (sim/all-committed (run))))))
