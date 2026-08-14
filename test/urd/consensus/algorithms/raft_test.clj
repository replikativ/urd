(ns urd.consensus.algorithms.raft-test
  "Scenario tests for Raft, ported from etcd-raft's `testdata` corpus.

  ## Why these are semantic and not byte-exact

  etcd-raft's golden files are transcripts of its `Ready` protocol: a batching
  layer that accumulates HardState, Entries, CommittedEntries and Messages
  between `Ready()` and `Advance()` calls, and a `stabilize` harness that drives
  it as a four-phase round-robin fixpoint. urd's protocol has no such layer --
  `step` returns effects for one input, immediately -- so half of the golden
  output (`> 1 handling Ready`, `Ready MustSync=true:`, the grouping of messages
  into batches) describes a mechanism this implementation deliberately does not
  have. Matching it byte for byte would mean building a Ready emulator in the
  test harness and then asserting on the emulator.

  So the corpus is ported as SEMANTIC assertions: the same scenario is set up,
  driven through urd's simulator, and the same conclusions are asserted --
  logs, commit indexes, per-peer progress, message counts, and the specific
  branch each test was written to pin. The `quorum/testdata` corpus, which is
  purely functional and has no Ready in it, IS ported byte-exactly; see
  `raft-quorum-corpus-test`.

  The tradeoff is real and worth stating: we lose the INFO/DEBUG lines that pin
  which branch of `stepLeader` was taken. Where a test exists specifically to
  pin a branch (the rejection-hint term skip, the heartbeat-response unpause) we
  assert on the observable consequence instead -- one round trip rather than
  seven, a message sent rather than not sent -- which is weaker but not by much."
  (:require [clojure.test :refer [deftest is testing]]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.node :as node]
            [urd.consensus.sim :as sim]))

;; ============================================================
;; Harness
;; ============================================================

(defn- entries
  "Build a log from a vector of terms: term `t` at 1-based position i."
  [terms]
  (vec (map-indexed (fn [i t] {:index (inc i) :term t :data nil}) terms)))

(defn make-sim
  "A Raft cluster in the simulator.

  `node-cfg` is per-peer configuration merged over the defaults; `config` is
  simulator configuration."
  [peers & [{:keys [node-cfg config seed]}]]
  (sim/make {:seed (or seed 3)
             :nodes (zipmap peers (repeat (raft/make)))
             :node-config (into {} (map (fn [p]
                                          [p (merge {:election-timeout 10
                                                     :heartbeat-timeout 3}
                                                    (get node-cfg p))]))
                                peers)
             :config (merge {:min-delay 1 :max-delay 1 :persist-latency 1} config)}))

(defn- role-of [s p] (:role (sim/node-state s p)))
(defn- term-of [s p] (:term (sim/node-state s p)))
(defn- log-terms [s p] (mapv :term (:log (sim/node-state s p))))
(defn- commit-of [s p] (:commit (sim/node-state s p)))

(defn- leaders
  "Live leaders. A crashed node's state is frozen, so it still claims to be
  leader; asking a corpse who is in charge gives the wrong answer."
  [s]
  (filterv #(and (not (contains? (:crashed s) %)) (= :leader (role-of s %)))
           (:peer-ids s)))

(defn- leader-of [s] (first (leaders s)))

(defn- has-leader? [s]
  (= 1 (count (leaders s))))

(defn- writes-of [s p] (get-in s [:storage p :writes]))

(defn committed-agree?
  "Do all nodes agree on the entry at every index they have both committed?

  `sim/agreement?` compares committed sequences POSITIONALLY, which is only the
  right test when every node starts from the same consensus index. A Raft
  cluster restored from divergent logs does not: a node whose commit index was
  already 8 emits its first `:commit` at index 9, while a node at commit 3 emits
  its first at 4, so position 0 of the two sequences is legitimately different
  while the nodes are in perfect agreement. Raft entries carry their own index,
  so we compare by index."
  [s]
  (let [by-index (fn [p] (into {} (map (juxt :index identity)) (sim/committed s p)))
        ms (mapv by-index (:peer-ids s))]
    (every? (fn [[a b]]
              (every? (fn [[i e]] (let [o (get b i)] (or (nil? o) (= e o)))) a))
            (for [a ms b ms] [a b]))))

;; ============================================================
;; testdata/single_node.txt
;; ============================================================

(deftest single-node-elects-itself-and-commits
  (testing "a one-node cluster campaigns, wins on its own vote, and commits

           The self-vote is the interesting part: it is only counted once the
           hard state is durable, so a single node still goes through the
           durability barrier before it can call itself leader."
    (let [s (sim/run (make-sim [:a]) 60)
          st (sim/node-state s :a)]
      (is (= :leader (:role st)))
      (is (= 1 (:term st)))
      (is (= [1] (log-terms s :a)) "the leader's empty term-1 entry")
      (is (= 1 (:commit st)) "and it commits with no peers to hear from")
      (is (= 1 (count (sim/committed s :a)))))))

(deftest single-node-persists-before-it-votes-for-itself
  (testing "the hard state write precedes the leadership claim"
    (let [s (sim/run (make-sim [:a]) 60)
          w (writes-of s :a)
          vote-write (first (filter #(= :a (get-in % [:writes :hard-state :vote])) w))]
      (is (some? vote-write) "the self-vote was written")
      (is (:durable? vote-write)
          "and fsync'd: MustSync is (entries | vote changed | term changed)"))))

;; ============================================================
;; testdata/campaign.txt
;; ============================================================

(deftest campaign-elects-one-leader-and-replicates
  (testing "three nodes, one election, the empty entry replicated everywhere"
    (let [s (sim/run (make-sim [:a :b :c]) 120)]
      (is (has-leader? s) "exactly one leader")
      (is (= 1 (term-of s (leader-of s))))
      (doseq [p [:a :b :c]]
        (is (= [1] (log-terms s p)) (str p " has the leader's entry"))
        (is (= 1 (commit-of s p)) (str p " committed it")))
      (is (sim/agreement? s)))))

(deftest a-follower-votes-at-most-once-per-term
  (testing "the vote is recorded in hard state and never changed within a term"
    (let [s (sim/run (make-sim [:a :b :c]) 120)]
      (doseq [p [:a :b :c]]
        (let [votes (->> (writes-of s p)
                         (keep #(get-in % [:writes :hard-state]))
                         (filter :vote)
                         (group-by :term))]
          (doseq [[term hss] votes]
            (is (= 1 (count (distinct (map :vote hss))))
                (str p " cast more than one distinct vote in term " term))))))))

;; ============================================================
;; testdata/prevote.txt
;; ============================================================

(deftest prevote-stops-a-rejoining-node-from-bumping-the-term
  (testing "a node isolated long enough to campaign repeatedly must not disrupt
            the cluster when it comes back

            Without PreVote the isolated node returns with an inflated term, the
            leader sees it and steps down, and the cluster pays an election it
            did not need. With PreVote the isolated node cannot raise its own
            term at all, because nobody will grant a pre-vote to a node whose
            log is behind."
    (let [s0 (sim/run (make-sim [:a :b :c]) 120)
          lead (leader-of s0)
          odd (first (remove #{lead} [:a :b :c]))
          ;; Isolate one follower for a long time; it will pre-campaign
          ;; repeatedly and get nowhere.
          s1 (-> s0 (sim/partition-network [#{odd} (set (remove #{odd} [:a :b :c]))])
                 (sim/run 300))]
      (is (= 1 (term-of s1 odd))
          "the isolated node's term did not move: PreVote never commits to a term")
      (is (= lead (leader-of s1)) "and the majority side kept its leader")
      (let [s2 (-> s1 sim/heal (sim/run 120))]
        (is (= lead (leader-of s2)) "rejoining caused no election")
        (is (= 1 (term-of s2 lead)) "and no term bump")))))

(deftest without-prevote-a-rejoining-node-does-disrupt
  (testing "the same scenario with PreVote off, to show the test has teeth

           This is the control: if this passed identically, the PreVote test
           above would be asserting nothing."
    (let [cfg (zipmap [:a :b :c] (repeat {:pre-vote? false}))
          s0 (sim/run (make-sim [:a :b :c] {:node-cfg cfg}) 120)
          lead (leader-of s0)
          odd (first (remove #{lead} [:a :b :c]))
          s1 (-> s0 (sim/partition-network [#{odd} (set (remove #{odd} [:a :b :c]))])
                 (sim/run 300))]
      (is (> (term-of s1 odd) 1)
          "without PreVote the isolated node freely inflates its term"))))

;; ============================================================
;; testdata/heartbeat_resp_recovers_from_probing.txt
;; ============================================================

(deftest heartbeat-response-unpauses-a-probing-peer
  (testing "a probe lost to a partition must not throttle a peer forever

           `maybeSendAppend` refuses to send while a probe is outstanding. If
           the probe was dropped, nothing ever clears that flag except the
           heartbeat response path (`raft.go:1581`). Omitting it wedges the peer
           permanently -- which is exactly what happened in development here."
    (let [peers [:a :b :c :d :e]
          s0 (sim/run (make-sim peers) 200)
          lead0 (leader-of s0)
          odd (first (remove #{lead0} peers))
          ;; Isolate a follower, then take out the leader so the remaining
          ;; three elect a new one. A NEW leader resets every peer's progress to
          ;; :probe, so its first message to the isolated node is a probe -- and
          ;; a probe with entries sets the pause.
          s1 (-> s0
                 (sim/partition-network [#{odd} (set (remove #{odd} peers))])
                 (sim/crash lead0)
                 (sim/run 300))
          lead1 (leader-of s1)]
      (is (some? lead1) "the majority side elected a new leader")
      (is (true? (get-in (sim/node-state s1 lead1) [:progress odd :flow-paused?]))
          "the isolated peer is paused after an unanswered probe")
      (let [s2 (-> s1 sim/heal (sim/run 300))]
        (is (false? (get-in (sim/node-state s2 lead1) [:progress odd :flow-paused?]))
            "and the heartbeat response cleared it")
        (is (= (log-terms s2 lead1) (log-terms s2 odd)) "so the peer caught up")))))

;; ============================================================
;; testdata/lagging_commit.txt
;; ============================================================

(deftest a-lagging-follower-learns-the-commit-index
  (testing "a follower that misses the append carrying a commit index still
            learns it, from the next append or heartbeat"
    (let [s0 (sim/run (make-sim [:a :b :c]) 120)
          lead (leader-of s0)
          odd (first (remove #{lead} [:a :b :c]))
          ;; Drop everything to one follower while several entries commit.
          s1 (-> s0
                 (sim/partition-network [#{odd} (set (remove #{odd} [:a :b :c]))])
                 (as-> s (reduce (fn [s' i] (sim/inject s' lead (node/value-ready {:v i})))
                                 s (range 5)))
                 (sim/run 60))]
      (is (< (commit-of s1 odd) (commit-of s1 lead))
          "the isolated follower is behind on commit")
      (let [s2 (-> s1 sim/heal (sim/run 120))]
        (is (= (commit-of s2 lead) (commit-of s2 odd))
            "and catches up once it can hear the leader again")
        (is (= (sim/committed s2 lead) (sim/committed s2 odd))
            "committing exactly the same entries, in the same order")))))

;; ============================================================
;; testdata/probe_and_replicate.txt -- the Figure 7 divergence
;; ============================================================

(def figure-7
  "Raft paper Figure 7, minus the index shift etcd applies for its bootstrap
  snapshot. Every follower diverges from the leader in a different way: short,
  extended, and conflicting-at-a-higher-term."
  {:n1 [1 1 1 4 4 5 5 6 6 6]
   :n2 [1 1 1 4 4 5 5 6 6]
   :n3 [1 1 1 4]
   :n4 [1 1 1 4 4 5 5 6 6 6 6]
   :n5 [1 1 1 4 4 5 5 6 7 7 7 7]
   :n6 [1 1 1 4 4 4 4]
   :n7 [1 1 1 2 2 2 3 3 3 3 3]})

(def ^:private figure-7-commit
  "Commit indexes consistent with the logs above: no node may have committed an
  entry that a later leader will truncate, so a node's commit must sit at or
  below its first point of divergence."
  {:n1 8 :n2 8 :n3 3 :n4 8 :n5 8 :n6 3 :n7 3})

(defn- figure-7-sim []
  (let [peers (vec (sort (keys figure-7)))]
    (make-sim peers
              {:node-cfg (into {} (map (fn [p]
                                         [p {:initial-log (entries (figure-7 p))
                                             :initial-term (last (figure-7 p))
                                             :initial-commit (figure-7-commit p)
                                             ;; n1 times out first, so the
                                             ;; election is deterministic.
                                             :election-timeout (if (= p :n1) 5 60)}]))
                               peers)})))

(deftest figure-7-converges-on-the-new-leaders-log
  (testing "a new leader overwrites every divergent suffix and catches everyone up"
    (let [s (sim/run (figure-7-sim) 400)
          lead (leader-of s)]
      (is (= :n1 lead) "n1 was elected -- its log is the most up to date among the majority")
      (is (= (conj (figure-7 :n1) 8) (log-terms s :n1))
          "the new leader appended one empty entry at its own term")
      (doseq [p (keys figure-7)]
        (is (= (log-terms s :n1) (log-terms s p))
            (str p " converged on the leader's log")))
      (is (= 11 (commit-of s :n1)) "and the whole log committed")
      (is (committed-agree? s)))))

(deftest figure-7-truncates-explicitly
  (testing "every divergent follower issues a truncate-from, and never below its
            own commit index

            etcd-raft leaves this implicit: storage has to notice an append at a
            lower index and infer a truncation. Making it explicit is the point
            of `:truncate-from`, and this asserts it actually gets set."
    (let [s (sim/run (figure-7-sim) 400)]
      ;; n4 (one entry too many), n5 (a term-7 tail), n6 (term-4 tail) and n7
      ;; (a whole term-2/3 history) all diverge; n2 and n3 are prefixes.
      (doseq [p [:n4 :n5 :n6 :n7]]
        (let [truncs (keep :truncate-from (writes-of s p))]
          (is (seq truncs) (str p " must have truncated"))
          (is (every? #(> % (figure-7-commit p)) truncs)
              (str p " truncated at or below its commit index, which is a "
                   "safety violation, not a recoverable state"))))
      (doseq [p [:n1 :n2 :n3]]
        (is (empty? (keep :truncate-from (writes-of s p)))
            (str p " has no divergent suffix and must not truncate"))))))

(deftest reject-hints-skip-whole-terms
  (testing "n7's log diverges at index 4 with HIGHER terms than the leader's,
            so naive probing would take one round trip per index

            The follower computes the hint (`findConflictByTerm` on its side)
            and the leader consumes it (`findConflictByTerm` on its side). With
            both halves working, n7 goes from a rejected probe at index 11 to a
            successful append anchored at index 3 in a single round trip."
    (let [s (sim/run (figure-7-sim) 400)
          n7-rejections (->> (:trace s)
                             (filter #(and (= :n7 (:peer %))
                                           (string? (:message %))
                                           (re-find #"rejected app" (:message %))))
                             count)]
      ;; n7 diverges from index 4 to 11: eight indexes. Probing one at a time
      ;; would be eight rejections; the term-skipping optimisation makes it one
      ;; or two.
      (is (<= n7-rejections 2)
          (str "n7 rejected " n7-rejections
               " appends; the term-skip optimisation should keep this at 1-2"))
      (is (pos? n7-rejections) "but it must reject at least once"))))

(deftest a-longer-log-does-not-win-an-election
  (testing "n4 and n5 have longer logs than n1, and n5's has a higher last term

           n5 must not lose data silently: it has an uncommitted term-7 tail
           that a term-8 leader with a shorter log is entitled to overwrite,
           because those entries were never committed. That is Raft 5.4.1 doing
           its job -- n1 wins only because a majority of logs are no more up to
           date than its own."
    (let [s (sim/run (figure-7-sim) 400)]
      (is (= :n1 (leader-of s)))
      (is (= 1 (count (leaders s))) "and only one leader")
      ;; n5's term-7 entries are gone; they were never committed.
      (is (not-any? #{7} (log-terms s :n5))))))

;; ============================================================
;; Election safety, stated directly
;; ============================================================

(deftest at-most-one-leader-per-term
  (testing "across a partition that produces two leaders, their terms differ"
    (let [s0 (sim/run (make-sim [:a :b :c :d :e]) 200)
          lead (leader-of s0)
          minority #{lead (first (remove #{lead} [:a :b :c :d :e]))}
          s1 (-> s0
                 (sim/partition-network [minority (into #{} (remove minority) [:a :b :c :d :e])])
                 (sim/run 300))
          by-term (group-by #(term-of s1 %) (leaders s1))]
      (is (<= 1 (count (leaders s1))) "the majority side elects someone")
      (doseq [[term ls] by-term]
        (is (= 1 (count ls)) (str "two leaders in term " term ": " ls))))))

;; ============================================================
;; The durability barrier
;; ============================================================

(deftest a-crash-before-fsync-loses-nothing-committed
  (testing "crash a leader between the append and the fsync, restart, and check
            that no committed entry vanished

            This is the test the whole `persist-then` design exists for. The
            leader appends, the write is in flight, the process dies. The
            entries that never reached disk are genuinely gone on restart -- and
            they must be entries that were never committed, because an entry is
            only counted toward the quorum once the leader's own write is
            durable (the self-ack)."
    (let [;; A slow fsync widens the window between issue and completion.
          s0 (sim/run (make-sim [:a :b :c] {:config {:persist-latency 6}}) 200)
          lead (leader-of s0)
          committed-before (sim/committed s0 lead)
          ;; Append without letting the write land.
          s1 (-> s0
                 (sim/inject lead (node/value-ready {:v :doomed}))
                 (sim/advance))
          _ (is (seq (get-in s1 [:pending-persist lead]))
                "the write must still be in flight for this test to mean anything")
          s2 (sim/crash s1 lead)
          ;; Let the rest of the cluster carry on, then bring the leader back.
          s3 (-> s2 (sim/run 300) (sim/restart lead) (sim/run 300))
          restored (sim/node-state s3 lead)]
      (is (some? restored))
      (is (>= (count (sim/committed s3 lead)) (count committed-before))
          "nothing that was committed before the crash was lost")
      (is (= (take (count committed-before) (sim/committed s3 lead))
             (vec committed-before))
          "and the committed prefix is unchanged, not merely the same length")
      (is (sim/agreement? s3)))))

(deftest a-restart-restores-term-and-vote-from-disk
  (testing "hard state survives, in-memory state does not"
    (let [s0 (sim/run (make-sim [:a :b :c]) 200)
          lead (leader-of s0)
          term-before (term-of s0 lead)
          s1 (-> s0 (sim/crash lead) (sim/restart lead))
          st (sim/node-state s1 lead)]
      (is (= term-before (:term st)) "the term came back from disk")
      (is (= :follower (:role st)) "but leadership did not -- it is not durable")
      (is (= (log-terms s0 lead) (mapv :term (:log st)))
          "and the log came back, since every entry was fsync'd before it was acked"))))

(deftest a-stale-persist-completion-is-a-no-op
  (testing "a completion whose epoch no longer matches the term is dropped

           The ABA hazard from `rawnode.go:266-363`: two writes covering the
           same indexes across a leader change. If the older completion were
           honoured it would mark durable a region that the newer append has
           since overwritten."
    (let [st (:state (node/init (raft/make) {:peer-id :a :validators [:a :b :c]}))
          ;; Pretend a write was issued at term 1 and the node has since moved on.
          st (assoc st :pending-writes [{:epoch 1 :last-index 5}] :term 7 :stable 0)
          {st' :state} (node/step (raft/make) st (node/persisted 0 1))]
      (is (= 0 (:stable st')) "the stale completion did not advance durability")
      (is (empty? (:pending-writes st')) "but it was consumed, not left in the queue")
      (is (= 7 (:term st')) "and it is a no-op, not an error"))))

;; ============================================================
;; Restart replay
;; ============================================================

(deftest replay-reconstructs-a-truncated-log
  (testing "the durable write log replays to the same log the node had

           A merge-based restore cannot express this: write A appends indexes
           4-8, write B truncates from 4 and appends a different 4-6. Merging
           the two `:entries` values gives nonsense; replaying them in order
           gives the right answer."
    (let [s (sim/run (figure-7-sim) 400)]
      (doseq [p [:n5 :n7]]
        (let [before (log-terms s p)
              s' (-> s (sim/crash p) (sim/restart p))
              after (mapv :term (:log (sim/node-state s' p)))]
          (is (= before after)
              (str p ": replaying the write log did not reproduce its log")))))))
