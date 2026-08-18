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

(deftest repeated-pre-vote-rounds-redraw-the-election-timeout
  (testing "PreVote deliberately does NOT bump the term -- that is its entire
            point (`become-pre-candidate`, `raft.go:917-931`) -- so keying the
            randomized election timeout on (id, term) alone makes it CONSTANT
            across pre-vote rounds.

            Two nodes that split a pre-vote would then re-campaign after exactly
            the same interval, split again, and repeat forever, deterministically,
            with no term ever advancing to break the tie. etcd redraws from
            `globalRand` on every `reset` and has no such case; the term-keyed
            version happened to resolve repeated splits only in the one
            configuration where the term moves.

            Here the same node campaigns three times at an unchanged term. The
            timeouts it arms must not all be equal."
    (let [impl (raft/make)
          st (:state (node/init impl {:peer-id :a :validators [:a :b :c]
                                      :pre-vote? true}))
          timeouts (fn [st n]
                     (loop [st st, i 0, acc []]
                       (if (= i n)
                         [st acc]
                         (let [{st' :state fx :effects}
                               (node/step impl st (node/timer-fired :election))
                               t (->> fx
                                      (filter #(and (= :set-timer (node/effect-kind %))
                                                    (= :election (:timer-id (node/effect-params %)))))
                                      first node/effect-params :after-ticks)]
                           (recur st' (inc i) (cond-> acc t (conj t)))))))
          [st' ts] (timeouts st 6)]
      (is (= 0 (:term st')) "the term never moved, which is what makes this bite")
      (is (= :pre-candidate (:role st')))
      (is (= 6 (count ts)) "every round arms a timer")
      (is (< 1 (count (distinct ts)))
          (str "all six pre-vote rounds armed the same timeout " (first ts)
               " -- a deterministic livelock")))))

(deftest three-overlapping-appends-across-three-terms
  (testing "etcd's `async_storage_writes_append_aba_race.txt`, as a scenario.

            The corpus itself is a datadriven script over etcd's `Ready` struct
            and its exact message rendering, neither of which urd has, so it
            cannot be replayed verbatim. What ports is the SHAPE, which is the
            part that found bugs: three appends covering the SAME INDEXES at
            three different terms, all in flight at once, completing out of
            order.

            Its steps 5, 7 and 9 are the point. A node appends {term 1, index 12}
            asynchronously; a new leader at term 2 overwrites index 12 while that
            write is still in flight; a third leader at term 3 overwrites it
            again. Then the FIRST write completes. Its completion is not evidence
            that index 12 is durable -- the entries it covered have been replaced
            twice, and the replacements are themselves still in the pipeline. As
            the corpus puts it: a future read from storage might otherwise see
            the entries from step 5 before they have been replaced by those from
            step 7.

            Two guards have to hold together, and each was wrong here once. The
            epoch witness must compare the write's OWN term against the CURRENT
            term -- comparing it against the echoed epoch is a tautology, which
            is how that guard came to be disabled. And completions must be
            correlated by TOKEN, because they do not arrive in issue order: this
            test delivers them 1, 3, 2 for exactly that reason."
    (let [impl (raft/make)
          st (:state (node/init impl {:peer-id :a :validators [:a :b :c]}))
          ;; Three writes over the same index, issued at successive terms, all
          ;; outstanding. Node is now at term 3, so only the third is current.
          st (assoc st
                    :pending-writes {10 {:epoch 1 :last-index 12 :durable? true}
                                     11 {:epoch 2 :last-index 12 :durable? true}
                                     12 {:epoch 3 :last-index 12 :durable? true}}
                    :next-write-token 13
                    :term 3
                    :stable 0)
          step (fn [st token epoch] (node/step impl st (node/persisted token epoch)))
          ;; Out of issue order, which is what the simulator actually produces.
          r1 (step st 10 1)
          r2 (step (:state r1) 12 3)
          r3 (step (:state r2) 11 2)]
      (is (= 0 (:stable (:state r1)))
          "the term-1 completion must not mark index 12 durable: those entries
           were overwritten twice and the replacements are still in flight")
      (is (= 12 (:stable (:state r2)))
          "the term-3 completion is the current one and does advance durability")
      (is (= 12 (:stable (:state r3)))
          "and the term-2 completion, arriving last, must not move it BACK")
      (is (empty? (filter #(= :commit (node/effect-kind %)) (:effects r1)))
          "nothing may be handed to the application on a superseded completion")
      ;; Every completion was attributed and removed by TOKEN, so none of the
      ;; three is still outstanding and none was consumed twice.
      (is (empty? (:pending-writes (:state r3)))
          "all three were correlated by token, in an order that is not issue
           order"))))

(deftest a-stale-persist-completion-is-a-no-op
  (testing "a completion whose epoch no longer matches the term is dropped

           The ABA hazard from `rawnode.go:266-363`: two writes covering the
           same indexes across a leader change. If the older completion were
           honoured it would mark durable a region that the newer append has
           since overwritten."
    (let [st (:state (node/init (raft/make) {:peer-id :a :validators [:a :b :c]}))
          ;; A write issued at term 1, correlated by token 0; the node has since
          ;; moved on to term 7 and is a candidate with an outstanding self-vote.
          ;; The stale record sits at a token BELOW the counter, which is what a
          ;; real run always produces -- tokens are minted monotonically, so a
          ;; write still in flight can never share a token with a later one.
          ;; (Placing it AT the counter makes the step's own new write reuse the
          ;; token, which is an artefact of hand-built state, not a live hazard.)
          st (assoc st
                    :pending-writes {99 {:epoch 1 :last-index 5 :durable? true}}
                    :next-write-token 100
                    :term 7
                    :stable 0
                    ;; Armed against the very write that is about to complete,
                    ;; so only the EPOCH guard can save us. Previously this was
                    ;; a bare index, which the completion satisfied by
                    ;; arithmetic rather than by attribution.
                    :self-ack {:through 5 :token 99})
          {st' :state} (node/step (raft/make) st (node/persisted 99 1))]
      ;; The assertions that matter are about the HARM, not about bookkeeping.
      ;; An earlier version of this test asserted only `(= 0 (:stable st'))` --
      ;; on a field that is written in three places and read in none, so deleting
      ;; the write would have left the test green while the guard did nothing.
      (is (= {:through 5 :token 99} (:self-ack st'))
          "a stale completion must NOT let the leader count its own entry durable")
      (is (= 0 (:stable st'))
          "nor advance durability")
      (is (not (contains? (:pending-writes st') 99))
          "the stale record is consumed, not left pending")
      (is (= 7 (:term st')) "and it is a no-op, not an error"))))

(deftest a-completion-is-matched-to-its-own-write-not-to-the-oldest
  (testing "out-of-order completions must not be misattributed.

           `:pending-writes` was a FIFO queue, popped from the front, on the
           assumption that interpreters complete writes in issue order. urd's own
           simulator does not: a non-durable write completes at the current tick
           while a durable one completes `persist-latency` ticks later, so a
           LATER buffered write routinely lands before an EARLIER fsync. Under
           FIFO that made the leader mark index 9 durable when only the write
           covering index 3 had landed."
    (let [st (:state (node/init (raft/make) {:peer-id :a :validators [:a :b :c]}))
          st (assoc st
                    :term 4
                    :stable 0
                    :self-ack {:through 9 :token 0}
                    ;; token 0 covers up to index 9 (still in flight),
                    ;; token 1 covers up to index 3 (lands first).
                    :pending-writes {0 {:epoch 4 :last-index 9 :durable? true}
                                     1 {:epoch 4 :last-index 3 :durable? true}})
          {st' :state} (node/step (raft/make) st (node/persisted 1 4))]
      (is (= 3 (:stable st'))
          "only the write that actually landed may advance durability")
      (is (= {:through 9 :token 0} (:self-ack st'))
          "the self-ack for index 9 must survive: its write has not landed")
      (is (contains? (:pending-writes st') 0)
          "and the in-flight write must still be outstanding"))))

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

;; ============================================================
;; The durability barrier, by carrier rather than by watermark
;; ============================================================

(deftest a-buffered-write-carrying-nothing-does-not-release-a-self-ack
  (testing "SAFETY. The port took etcd's durability WATERMARK -- release
            everything up to the last completed index -- without the FIFO
            precondition that makes it sound. etcd may do that because messages
            to one target are processed in order and `msgsAfterAppend` are
            attached as Responses to that specific `MsgStorageAppend`; our
            protocol explicitly declines to promise ordering, and our own
            simulator does not provide it.

            The result was that a step changing nothing durable still minted a
            write, that write carried no entries, and its completion released
            every gated commitment anyway."
    (let [st (:state (node/init (raft/make) {:peer-id :a :validators [:a :b :c]}))
          st (assoc st
                    :role :leader :term 4 :stable 0
                    ;; Armed by the append that carried entries (token 0),
                    ;; which is still in flight.
                    :self-ack {:through 3 :token 0}
                    ;; Above the outstanding tokens, or this step's own write
                    ;; reuses token 0 and overwrites the record under test.
                    :next-write-token 2
                    :pending-writes {0 {:epoch 4 :last-index 3 :durable? true}
                                     ;; A later commit-index-only write: no
                                     ;; entries, correctly not fsynced.
                                     1 {:epoch 4 :last-index 3 :durable? false}})
          {after-buffered :state} (node/step (raft/make) st (node/persisted 1 4))]
      (is (= {:through 3 :token 0} (:self-ack after-buffered))
          "the buffered write carried no entries to the platter, so it cannot
           make the leader's own entries durable")
      (is (= 0 (:stable after-buffered))
          "nor advance durability -- :stable means entries are on OUR disk")
      (let [{after-carrier :state} (node/step (raft/make) after-buffered
                                              (node/persisted 0 4))]
        (is (nil? (:self-ack after-carrier)) "the carrier releases it")
        (is (= 3 (:stable after-carrier)))))))

(deftest a-self-vote-is-released-only-by-the-write-that-carried-it
  (testing "SAFETY, and the finding this closes was recorded as ALREADY CLOSED.
            `consume-self-vote` took a `last-index` argument whose docstring
            said it ensured the completion belonged to a write issued at or
            after the vote; the parameter was `_`-prefixed and never read.

            An index would not have sufficed anyway: a candidate's vote write
            and the buffered write minted by the next rejected vote request
            have the SAME last index, so any index test passes."
    (let [st (:state (node/init (raft/make) {:peer-id :a :validators [:a :b :c]}))
          st (assoc st
                    :role :candidate :term 1 :votes {}
                    :self-vote {:term 1 :kind :vote :token 0}
                    :next-write-token 2
                    :pending-writes {0 {:epoch 1 :last-index 0 :durable? true}
                                     1 {:epoch 1 :last-index 0 :durable? false}})
          {other :state} (node/step (raft/make) st (node/persisted 1 1))]
      (is (some? (:self-vote other))
          "a write that did not carry the vote must not publish it")
      (is (empty? (:votes other)))
      (let [{carried :state} (node/step (raft/make) other (node/persisted 0 1))]
        (is (nil? (:self-vote carried)) "its own write does")
        (is (contains? (:votes carried) :a))))))

(deftest a-restart-announces-the-committed-prefix-rather-than-losing-it
  (testing "SAFETY. `:applied` starts at `commit`, so an entry committed but
            not yet DELIVERED -- the state `flush-commits` creates by holding
            delivery behind `:stable` -- would never be handed over at all.
            `resync` is the effect for a restarting node announcing what it
            believes its committed prefix to be; `commit` would append a second
            copy of it."
    (let [entries [{:index 1 :term 1 :data :x} {:index 2 :term 1 :data :y}]
          writes [{:writes {:hard-state {:term 1 :vote nil :commit 2}
                            :entries entries}
                   :durable? true}]
          {st :state fx :effects}
          (node/init (raft/make) {:peer-id :a :validators [:a :b :c]
                                  :restored {:durable {} :writes writes}})
          resyncs (filter #(= :resync (node/effect-kind %)) fx)]
      (is (= 2 (:commit st)))
      (is (= 1 (count resyncs)) "exactly one announcement")
      (is (= entries (:vertices (node/effect-params (first resyncs))))
          "carrying the whole committed prefix, in order")
      (is (empty? (filter #(= :commit (node/effect-kind %)) fx))
          "and NOT as a commit, which would duplicate the prefix"))))

(deftest a-fresh-node-announces-nothing
  (let [{fx :effects} (node/init (raft/make) {:peer-id :a :validators [:a :b :c]})]
    (is (empty? (filter #(#{:resync :commit} (node/effect-kind %)) fx))
        "there is no committed prefix to announce")))

;; ============================================================
;; Compaction
;; ============================================================

(defn- fresh-state
  "A node state to hang a log on, without driving an election to get one."
  []
  (:state (node/init (raft/make) {:peer-id :a :validators [:a :b :c]})))

(deftest compaction-keeps-indices-absolute
  (testing "the property everything else in this file depends on

           `:applied`, `:commit`, `:stable`, `:issued`, every `prev-index` on
           the wire and every `Progress` in the leader are ABSOLUTE indices. If
           compaction renumbered anything, all of them would be silently wrong
           at once -- which is why `:log` could not simply be trimmed and why
           this waited for the offset."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 51)] {:index i :term 1 :data i}))
                    :applied 40 :commit 40)
          c (raft/compact st 10)]
      (is (= 50 (raft/last-index st)))
      (is (= 50 (raft/last-index c))
          "the last index does not move when the vector shrinks")
      (is (= 20 (count (:log c))) "while the vector really did shrink")
      (is (= 30 (:log-base c)))
      (is (= 50 (:index (raft/entry-at c 50))) "the head is still addressable")
      (is (= 35 (:index (raft/entry-at c 35))) "and so is the middle")
      (is (nil? (raft/entry-at c 20)) "what was dropped reads as absent")))

  (testing "`:base-term` is why the boundary is not a permanent mismatch

           `prevLogTerm` matching has to work AT the boundary: a leader appends
           at `(prev-index = base)` and the follower must be able to answer.
           etcd keeps the same value as its dummy `ents[0]` and documents
           `Term` as valid on `[FirstIndex()-1, LastIndex()]`."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 21)] {:index i :term (if (< i 10) 3 7)}))
                    :applied 15 :commit 15)
          c (raft/compact st 5)]
      (is (= 10 (:log-base c)))
      (is (= 7 (raft/term-at c 10))
          "the term AT the boundary is retained, not lost with the entry")
      (is (nil? (raft/term-at c 5))
          "while a term below the boundary is honestly unknown, not zero --
           answering 0 would make a stale append appear to match")))

  (testing "compaction never passes `:applied`, whatever retention says"
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 51)] {:index i :term 1}))
                    :applied 10 :commit 40)]
      (is (= 0 (:log-base (raft/compact st 100)))
          "a retention larger than what is applied compacts nothing")
      (is (>= (:applied st) (:log-base (raft/compact st 0)))
          "and even zero retention stops at applied -- an entry the
           application has not seen cannot be reconstructed from anywhere")))

  (testing "a compacted log still appends, and the new entries are addressable
            at the indices they claim"
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 51)] {:index i :term 1}))
                    :applied 40 :commit 40)
          c (raft/compact st 10)
          grown (update c :log conj {:index 51 :term 1})]
      (is (= 51 (raft/last-index grown)))
      (is (= 51 (:index (raft/entry-at grown 51)))))))

(deftest a-checkpointed-log-restores-to-the-same-node
  (testing "the round trip that makes compaction worth anything

           `compact` bounds MEMORY. Until the durable log is rewritten too, a
           node whose in-memory log is twenty entries still replays twenty
           thousand on restart -- the store is the history whatever the state
           machine has forgotten.

           So: build a log, compact it, write `checkpoint-records`, and restore
           from ONLY those records. The node that comes back must be the node
           that went in -- same last index, same base, same boundary term, same
           entries, same hard state -- while the durable log is now two records
           instead of thousands."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 201)] {:index i :term 2 :data i}))
                    :applied 150 :commit 150 :term 2 :vote :a)
          compacted (raft/compact st 10)
          records (raft/checkpoint-records compacted)
          ;; Restore a fresh node from the checkpoint alone.
          restored (:state (node/init (raft/make)
                                      {:peer-id :a :validators [:a :b :c]
                                       :restored {:durable {} :writes records}}))]
      (is (= 2 (count records))
          "two records stand in for two hundred entries")
      (is (= (:log-base compacted) (:log-base restored))
          "the boundary survives the round trip")
      (is (= (:base-term compacted) (:base-term restored))
          "and so does its term, or `prevLogTerm` matching breaks at the seam")
      (is (= (raft/last-index compacted) (raft/last-index restored))
          "the last index is unchanged -- indices are absolute, and a restore
           that renumbered them would corrupt every Progress in the cluster")
      (is (= (mapv :index (:log compacted)) (mapv :index (:log restored)))
          "the entries still held come back at the indices they claim")
      (is (= 2 (:term restored)))
      (is (= :a (:vote restored)) "and the hard state with them")))

  (testing "a checkpoint followed by further appends replays in order

           `replay`'s position arithmetic had to become base-aware for this:
           computing `(dec index)` renumbers a compacted log back to base 0, on
           the one path -- restore -- where being wrong is worst."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 101)] {:index i :term 3}))
                    :applied 80 :commit 80 :term 3)
          compacted (raft/compact st 5)
          records (conj (vec (raft/checkpoint-records compacted))
                        {:writes {:entries [{:index 101 :term 3} {:index 102 :term 3}]}
                         :durable? true})
          restored (:state (node/init (raft/make)
                                      {:peer-id :a :validators [:a :b :c]
                                       :restored {:durable {} :writes records}}))]
      (is (= 102 (raft/last-index restored)))
      (is (= 102 (:index (raft/entry-at restored 102))))
      (is (= 75 (:log-base restored)) "the base is not disturbed by later appends")
      (is (nil? (raft/entry-at restored 70)) "and what was compacted stays gone"))))

(deftest a-compacted-restart-announces-nothing-rather-than-a-truncated-prefix
  (testing "SAFETY, and the one place compaction and recovery collide.

           `resync` replaces the consumer's view WHOLESALE -- that is what makes
           it the right effect for a restart, and what makes it lethal here. A
           node that has compacted no longer holds its committed prefix; it
           holds the tail. Announcing that tail says `here is everything that
           was committed`, and a ledger obeying it drops every transaction below
           the boundary. Compaction succeeding would cause data loss on the next
           restart.

           The first version of this did exactly that and was caught only
           because `subvec` threw: `commit` is an absolute index and the vector
           had been trimmed. An off-by-base that happened to be out of bounds.
           Had the boundary been smaller than the commit index, it would have
           announced a wrong prefix silently.

           Announcing nothing keeps what the consumer has, which is correct but
           incomplete: a node that holds entries 141-200 cannot say so. That
           needs `resync` to carry a floor, which does not exist yet."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 201)] {:index i :term 2 :data i}))
                    :applied 150 :commit 150 :term 2)
          records (raft/checkpoint-records (raft/compact st 10))
          {rst :state fx :effects}
          (node/init (raft/make) {:peer-id :a :validators [:a :b :c]
                                  :restored {:durable {} :writes records}})]
      (is (pos? (:log-base rst)) "the restored node really is compacted")
      (is (empty? (filter #(#{:resync :commit} (node/effect-kind %)) fx))
          "and says nothing about a prefix it no longer holds")))

  (testing "while an UNcompacted restart still announces -- the suppression is
            conditional on having thrown history away, not on having restored"
    (let [entries (vec (for [i (range 1 6)] {:index i :term 1 :data i}))
          records [{:writes {:hard-state {:term 1 :vote nil :commit 5}
                             :entries entries}
                    :durable? true}]
          {rst :state fx :effects}
          (node/init (raft/make) {:peer-id :a :validators [:a :b :c]
                                  :restored {:durable {} :writes records}})]
      (is (zero? (:log-base rst)))
      (is (= entries (:vertices (node/effect-params
                                 (first (filter #(= :resync (node/effect-kind %))
                                                fx)))))))))

;; ============================================================
;; The consumer says where it is
;; ============================================================

(deftest a-consumer-that-reports-its-position-is-caught-up-exactly
  (testing "`resync` exists because a restarting node has to GUESS what its
            consumer holds, and both guesses are wrong somewhere. Re-announcing
            the whole prefix is impossible once the log is compacted;
            announcing nothing -- the safe alternative -- silently drops
            entries that were committed but never delivered, which is the very
            thing `resync` was introduced to fix.

           etcd resolves this by taking `Config.Applied` from the application
           and warning that, unset, raft `might return previous applied
           entries`. This is that, as a COUNT: the consumer counts vertices and
           knows nothing about Raft's numbering, and for this algorithm the two
           coincide.

           The gap goes out as ORDINARY commits, which append rather than
           replace -- so unlike `resync` it cannot truncate a consumer that is
           ahead of us."
    (let [entries (vec (for [i (range 1 21)] {:index i :term 1 :data i}))
          writes [{:writes {:hard-state {:term 1 :vote nil :commit 20}
                            :entries entries}
                   :durable? true}]
          init-with (fn [delivered]
                      (node/init (raft/make)
                                 (cond-> {:peer-id :a :validators [:a :b :c]
                                          :restored {:durable {} :writes writes}}
                                   delivered (assoc :delivered-through delivered))))]

      (testing "a consumer at 12 receives exactly 13..20"
        (let [{st :state fx :effects} (init-with 12)
              commits (filter #(= :commit (node/effect-kind %)) fx)
              handed (mapcat #(:vertices (node/effect-params %)) commits)]
          (is (= 12 (:applied st)) "we resume from where the consumer is")
          (is (= (range 13 21) (map :index handed))
              "the gap and nothing else -- no re-delivery, no omission")
          (is (empty? (filter #(= :resync (node/effect-kind %)) fx))
              "and NOT as a resync, which would replace the consumer's view
               rather than extend it")))

      (testing "a consumer already up to date receives nothing"
        (let [{st :state fx :effects} (init-with 20)]
          (is (= 20 (:applied st)))
          (is (empty? (filter #(#{:commit :resync} (node/effect-kind %)) fx)))))

      (testing "a consumer AHEAD of our commit index is not truncated"
        (let [{st :state fx :effects} (init-with 50)]
          (is (= 20 (:applied st)) "clamped to what we can actually prove")
          (is (empty? (filter #(#{:commit :resync} (node/effect-kind %)) fx))
              "nothing is taken back -- the entries it holds were on our disk
               before we handed them over, and Raft never overwrites a
               committed entry")))

      (testing "no report at all falls back to announcing the prefix"
        (let [{fx :effects} (init-with nil)]
          (is (seq (filter #(= :resync (node/effect-kind %)) fx))
              "the old behaviour is still there for a consumer that cannot
               say where it is"))))))

(deftest a-compacted-node-still-serves-a-consumer-that-is-behind
  (testing "this is the hole that suppressing `resync` opened, and the reason
            `:delivered-through` is not merely tidier.

           A compacted node announced NOTHING on restart, so anything
           committed but not yet delivered was lost with no error. Compaction
           does not interfere here: retention is measured from `:applied`, so
           the undelivered window is above the boundary by construction."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 201)] {:index i :term 2 :data i}))
                    :applied 150 :commit 150 :term 2)
          records (raft/checkpoint-records (raft/compact st 10))
          {rst :state fx :effects}
          (node/init (raft/make) {:peer-id :a :validators [:a :b :c]
                                  :restored {:durable {} :writes records}
                                  :delivered-through 145})
          handed (mapcat #(:vertices (node/effect-params %))
                         (filter #(= :commit (node/effect-kind %)) fx))]
      (is (pos? (:log-base rst)) "genuinely compacted")
      (is (= (range 146 151) (map :index handed))
          "the five undelivered entries are handed over, from a node that
           previously said nothing at all"))))

(deftest a-consumer-behind-the-retention-boundary-is-told-so
  (testing "the one case that cannot be served. Compaction threw those entries
            away, and the honest answer is to say so rather than hand over a
            gap-ridden suffix that a ledger would apply as if contiguous."
    (let [st (assoc (fresh-state)
                    :log (vec (for [i (range 1 201)] {:index i :term 2 :data i}))
                    :applied 150 :commit 150 :term 2)
          records (raft/checkpoint-records (raft/compact st 10))
          {fx :effects}
          (node/init (raft/make) {:peer-id :a :validators [:a :b :c]
                                  :restored {:durable {} :writes records}
                                  :delivered-through 3})
          logs (filter #(= :log (node/effect-kind %)) fx)]
      (is (empty? (filter #(#{:commit :resync} (node/effect-kind %)) fx))
          "nothing is handed over, because nothing contiguous can be")
      (is (some #(= :consumer-behind-retention (:event (:message (node/effect-params %))))
                logs)
          (str "and it is reported: " (mapv #(node/effect-params %) logs))))))

;; ============================================================
;; Membership changes
;; ============================================================

(defn- leader-at [validators]
  (let [{st :state} (node/init (raft/make) {:peer-id :a :validators validators})]
    (-> st
        (assoc :role :leader :term 1 :lead :a
               :progress (into {} (map (fn [p] [p {:match 0 :next 1 :state :replicate}]))
                               validators)))))

(deftest a-membership-change-activates-when-its-entry-COMMITS
  (testing "the thesis activates at ADD, etcd at APPLY, and both are safe given
            one-at-a-time -- etcd says so directly: `equivalent in terms of
            safety, since the old and new configurations are guaranteed to
            overlap`.

           Commit is chosen here because `commit-to` is the single chokepoint
           through which the leader AND every follower advance, so every node
           activates at the same LOG POSITION even though they reach it at
           different moments. Wall-clock agreement is neither available nor
           needed.

           It also avoids the hazard etcd carries: their active config is their
           APPLIED config, and applied trails committed by an unbounded,
           application-controlled amount. urd's state machine has no such lag."
    (let [st (-> (leader-at [:a :b :c])
                 (assoc :log [{:index 1 :term 1
                               :data {:validator-updates [{:id :d :power 1}]}}]
                        :commit 0))]
      (is (= [:a :b :c] (:validators st)) "not yet -- the entry is uncommitted")
      (let [after (#'raft/commit-to (assoc st :fx {:logs []}) 1)]
        (is (= [:a :b :c :d] (:validators after))
            "committed, so the set changes")
        (is (contains? (:progress after) :d)
            "and the newcomer gets a Progress entry, or the leader cannot
             replicate to it")))))

(deftest a-removed-validator-loses-its-progress
  (testing "a stale Progress entry for a removed peer keeps contributing its
            `:match` to `committed-index`, so the commit index could be
            advanced by a node that is no longer a validator. That is a quorum
            computed over the wrong set."
    (let [st (-> (leader-at [:a :b :c])
                 (assoc :log [{:index 1 :term 1
                               :data {:validator-updates [{:id :c :power 0}]}}]
                        :commit 0 :fx {:logs []}))
          after (#'raft/commit-to st 1)]
      (is (= [:a :b] (:validators after)))
      (is (not (contains? (:progress after) :c))
          "c is gone from Progress, not merely from the validator list"))))

(deftest only-one-membership-change-may-be-in-flight
  (testing "THE safety rule, and it is not the activation point.

           A configuration differing by a single voter always has majorities
           intersecting its predecessor's (thesis S4.1). Two changes in flight
           lose that: each could be committed by a majority of a DIFFERENT
           configuration, and the two quorums need not overlap.

           Measured against `:commit`, because that is where urd activates.
           etcd measures against `applied` because their active config is their
           applied config; pairing the check with the wrong index is how a
           fixed offset becomes unsound."
    (let [st (-> (leader-at [:a :b :c])
                 (assoc :log [{:index 1 :term 1
                               :data {:validator-updates [{:id :d :power 1}]}}]
                        :commit 0))
          ;; A second change while the first is uncommitted.
          {st' :state} (node/step (raft/make) st
                                  (node/value-ready {:validator-updates
                                                     [{:id :e :power 1}]}))]
      (is (= 1 (raft/last-index st'))
          "the second change is NOT appended while the first is uncommitted")

      (testing "and it is accepted once the first commits"
        (let [committed (#'raft/commit-to (assoc st :fx {:logs []}) 1)
              {st'' :state} (node/step (raft/make) (dissoc committed :fx)
                                       (node/value-ready {:validator-updates
                                                          [{:id :e :power 1}]}))]
          (is (= 2 (raft/last-index st''))
              "or the cluster could never change membership twice")))))

  (testing "an ordinary value is never blocked by a pending change"
    (let [st (-> (leader-at [:a :b :c])
                 (assoc :log [{:index 1 :term 1
                               :data {:validator-updates [{:id :d :power 1}]}}]
                        :commit 0))
          {st' :state} (node/step (raft/make) st (node/value-ready {:payload :ordinary}))]
      (is (= 2 (raft/last-index st'))
          "the rule is about CONFIGURATION changes, not about proposals"))))

(deftest a-multi-voter-change-enters-joint-consensus
  (testing "a single-voter change is safe because a configuration differing by
            one voter always has majorities intersecting its predecessor's. An
            ARBITRARY change has no such guarantee, so the overlap is
            manufactured instead: while joint, every quorum needs a majority of
            BOTH the old set and the new one.

           The joint state is itself just a configuration -- one value in the
           same lattice -- which is why entering needs no special decision
           type. `:outgoing` is the half being left."
    (let [st (leader-at [:a :b :c])
          {st' :state} (node/step (raft/make) st
                                  (node/value-ready {:validator-updates
                                                     [{:id :d :power 1}
                                                      {:id :e :power 1}]}))]
      (is (= 1 (raft/last-index st'))
          "accepted -- it used to be refused, before joint consensus existed")
      (is (empty? (:outgoing st'))
          "but not yet joint: the entry is appended, not committed")

      (testing "and committing it enters the joint configuration"
        (let [after (#'raft/commit-to (assoc st' :fx {:logs []}) 1)]
          (is (= [:a :b :c :d :e] (:validators after)) "the incoming half")
          (is (= [:a :b :c] (:outgoing after)) "and the half being left")
          (is (every? (set (keys (:progress after))) [:a :b :c :d :e])
              "Progress covers the UNION -- an outgoing-only peer still votes
               and still acks, and dropping it would make its half of the
               quorum unreachable")))))

  (testing "a single-voter change does NOT enter joint -- it does not need to"
    (let [st (leader-at [:a :b :c])
          {st' :state} (node/step (raft/make) st
                                  (node/value-ready {:validator-updates
                                                     [{:id :d :power 1}]}))
          after (#'raft/commit-to (assoc st' :fx {:logs []}) 1)]
      (is (= [:a :b :c :d] (:validators after)))
      (is (empty? (:outgoing after))
          "the intersection argument holds for free, so paying for a joint
           transition would be pure cost")))

  (testing "re-weighting an EXISTING validator is not a membership change"
    (let [st (leader-at [:a :b :c])
          {st' :state} (node/step (raft/make) st
                                  (node/value-ready {:validator-updates
                                                     [{:id :a :power 5}
                                                      {:id :b :power 7}]}))
          after (#'raft/commit-to (assoc st' :fx {:logs []}) 1)]
      (is (= 1 (raft/last-index st')))
      (is (empty? (:outgoing after))
          "who is in the set is unchanged, so the intersection argument is
           untouched -- etcd has no notion of power and cannot answer this
           for us"))))

(deftest a-quorum-while-joint-needs-BOTH-halves
  (testing "the property that replaces the single-voter intersection argument.

           Acks from a majority of the new set alone must NOT commit, or the
           old configuration could have committed something different with its
           own majority -- two disjoint quorums, which is the whole thing joint
           consensus exists to prevent."
    (let [;; Joint: leaving [:a :b :c], entering [:a :d :e].
          st (-> (leader-at [:a :b :c])
                 (assoc :validators [:a :d :e] :outgoing [:a :b :c] :term 1)
                 (assoc :log [{:index 1 :term 1 :data {:v 1}}])
                 (assoc :progress (into {} (map (fn [p] [p {:match 0 :next 2 :state :replicate}]))
                                        [:a :b :c :d :e])))
          ;; A majority of the INCOMING half only (:a :d :e all acked).
          incoming-only (assoc st :progress
                               (merge (:progress st)
                                      {:a {:match 1 :next 2 :state :replicate}
                                       :d {:match 1 :next 2 :state :replicate}
                                       :e {:match 1 :next 2 :state :replicate}}))
          ;; Both halves: add :b so [:a :b] is a majority of [:a :b :c] too.
          both (assoc-in incoming-only [:progress :b] {:match 1 :next 2 :state :replicate})]
      (is (= 0 (raft/joint-committed-index [:a :d :e] [:a :b :c]
                                           (into {} (map (fn [[p pr]] [p (:match pr)]))
                                                 (:progress incoming-only))))
          "a majority of the new set alone commits nothing")
      (is (= 1 (raft/joint-committed-index [:a :d :e] [:a :b :c]
                                           (into {} (map (fn [[p pr]] [p (:match pr)]))
                                                 (:progress both))))
          "a majority of both halves commits")))

  (testing "and a non-joint configuration runs the same code path"
    (is (= 1 (raft/joint-committed-index [:a :b :c] []
                                         {:a 1 :b 1 :c 0}))
        "an empty outgoing half is neutral by construction -- which is why
         there is one code path rather than a branch that could disagree with
         itself")))
