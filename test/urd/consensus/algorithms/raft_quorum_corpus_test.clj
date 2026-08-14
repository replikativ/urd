(ns urd.consensus.algorithms.raft-quorum-corpus-test
  "Byte-exact port of etcd-raft's `quorum/testdata` conformance corpus.

  These four files are the highest value per line in the whole etcd-raft test
  suite, because they are purely functional: `committed cfg=(1,2,3)
  idx=(_,5,7)` and `vote cfg=(1,2) votes=(y,n,_)` are a total function of their
  arguments, with no scheduling, no time, and no I/O. So we can compare golden
  output character for character rather than asserting on state, and a
  divergence points at exactly one arithmetic bug.

  The corpus files themselves are vendored under `test/resources/etcd-raft/`
  (Apache 2.0, licence included alongside).

  Two subtleties the corpus is specifically designed to catch:

  - `_` means \"no information\", which is NOT index 0. A voter that has not
    reported and a voter that has reported index 0 give the same committed
    index, but they differ in the rendering (`?` versus `>`), and the test data
    forbids a literal `idx=0` precisely so the two cannot be confused.
  - The harness runs metamorphic checks: a plain majority config must agree with
    that config joined to the empty config, and with itself joined to itself;
    and a joint config must give the same answer with its halves swapped. Those
    are the properties that make `JointConfig` well-formed, and they are checked
    on every single case rather than being separate tests."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.node :as node]))

;; ============================================================
;; Rendering (etcd `quorum/majority.go` Describe, `quorum.Index.String`)
;; ============================================================

(defn- index->str
  "`quorum/quorum.go`: MaxUint64 renders as the infinity sign."
  [idx]
  (if (= idx raft/max-index) "∞" (str (long idx))))

(defn- describe
  "`quorum/majority.go:46-101`. A progress-bar table, one row per voter.

  The bar length is the row's rank in ascending index order, except that equal
  indices must get equal bars -- that carry-forward is the only fiddly part."
  [ids acked]
  (let [n (count ids)]
    (if (zero? n)
      ;; No trailing newline, so the committed index lands on the same line.
      "<empty majority quorum>"
      (let [info (->> ids
                      (map (fn [id] {:id id :idx (get acked id 0) :ok (contains? acked id)}))
                      (sort-by (juxt :idx :id))
                      vec)
            bars (reduce (fn [acc i]
                           (conj acc (if (< (:idx (nth info (dec i))) (:idx (nth info i)))
                                       i
                                       (nth acc (dec i)))))
                         [0]
                         (range 1 n))
            info (sort-by :id (map #(assoc %1 :bar %2) info bars))]
        (str (apply str (repeat n " ")) "    idx\n"
             (apply str
                    (for [{:keys [id idx ok bar]} info]
                      (str (if ok
                             (str (apply str (repeat bar "x")) ">"
                                  (apply str (repeat (- n bar) " ")))
                             (str "?" (apply str (repeat n " "))))
                           " " (format "%5d" (long idx))
                           "    (id=" (format "%x" (long id)) ")\n"))))))))

;; ============================================================
;; Directive parsing (etcd `quorum/datadriven_test.go`)
;; ============================================================

(def ^:private token-re #"[a-z]+(?:=(?:\([^)]*\)|\S+))?")

(defn- parse-args [line]
  (let [[cmd & args] (re-seq token-re line)]
    [cmd
     (for [a args]
       (let [[k v] (str/split a #"=" 2)]
         [k (cond
              (nil? v) []
              (str/starts-with? v "(") (->> (subs v 1 (dec (count v)))
                                            (#(str/split % #","))
                                            (map str/trim)
                                            (remove str/blank?)
                                            vec)
              :else [v])]))]))

(defn- make-lookuper
  "`quorum/datadriven_test.go`. Positional values map onto ids in declaration
  order (cfg then cfgj), skipping ids already assigned -- so an id named in both
  halves consumes exactly one slot. The 0 sentinel is dropped afterwards, which
  is what turns `_` into \"absent\" rather than \"acked 0\"."
  [vals ids idsj]
  (loop [remaining (concat ids idsj), p 0, m {}]
    (if (or (empty? remaining) (>= p (count vals)))
      (into {} (remove (comp zero? val)) m)
      (let [id (first remaining)]
        (if (contains? m id)
          (recur (rest remaining) p m)
          (recur (rest remaining) (inc p) (assoc m id (nth vals p))))))))

(defn- run-directive [line]
  (let [[cmd args] (parse-args line)
        st (reduce (fn [acc [k vs]]
                     (case k
                       "cfg" (update acc :ids into (map parse-long) vs)
                       "cfgj" (cond-> (assoc acc :joint? true)
                                (not= vs ["zero"]) (update :idsj into (map parse-long) vs))
                       "idx" (update acc :vals into
                                     (map #(if (= "_" %) 0 (parse-long %))) vs)
                       "votes" (update acc :vals into
                                       (map {"_" 0 "n" 1 "y" 2}) vs)
                       acc))
                   {:ids [] :idsj [] :vals [] :joint? false}
                   args)
        {:keys [ids idsj vals joint?]} st
        voters (distinct (concat ids idsj))]
    (if (not= (count voters) (count vals))
      (str "error: mismatched input for voters " (vec (sort voters)) ": " vals)
      (case cmd
        "committed"
        (let [acked (make-lookuper vals ids idsj)
              idx (if joint?
                    (raft/joint-committed-index ids idsj acked)
                    (raft/committed-index ids acked))
              checks (if joint?
                       ;; Swapping the halves of a joint config must not change
                       ;; the answer; `min` is commutative, so a failure here
                       ;; means the halves are not being treated symmetrically.
                       (let [sym (raft/joint-committed-index idsj ids acked)]
                         (when (not= sym idx)
                           [(str (index->str sym) " <-- via symmetry")]))
                       (concat
                        ;; A plain majority must agree with itself joined to the
                        ;; empty config (which relies on the empty config's
                        ;; committed index being the identity for `min`)...
                        (let [z (raft/joint-committed-index ids [] acked)]
                          (when (not= z idx)
                            [(str (index->str z) " <-- via zero-joint quorum")]))
                        ;; ...and with itself joined to itself.
                        (let [s (raft/joint-committed-index ids ids acked)]
                          (when (not= s idx)
                            [(str (index->str s) " <-- via self-joint quorum")]))
                        ;; Lowering a voter that is already below the committed
                        ;; index must not move the committed index.
                        (mapcat
                         (fn [id]
                           (let [iidx (get acked id 0)]
                             (when (and (> idx iidx) (pos? iidx))
                               (concat
                                (let [lo (assoc (select-keys acked ids) id (dec iidx))
                                      a (raft/committed-index ids lo)]
                                  (when (not= a idx)
                                    [(str (index->str a) " <-- overlaying " id "->" iidx)]))
                                (let [lo (assoc (select-keys acked ids) id 0)
                                      a (raft/committed-index ids lo)]
                                  (when (not= a idx)
                                    [(str (index->str a) " <-- overlaying " id "->0")]))))))
                         (sort ids))))]
          (str (describe (if joint? voters ids) acked)
               (apply str (map #(str % "\n") checks))
               (index->str idx) "\n"))

        "vote"
        (let [raw (make-lookuper vals ids idsj)
              votes (into {} (map (fn [[k v]] [k (not= v 1)])) raw)
              res (if joint?
                    (raft/joint-vote-result ids idsj votes)
                    (raft/vote-result ids votes))
              name* {:won "VoteWon" :lost "VoteLost" :pending "VotePending"}
              checks (when joint?
                       (let [sym (raft/joint-vote-result idsj ids votes)]
                         (when (not= sym res)
                           [(str (name* sym) " <-- via symmetry")])))]
          (str (apply str (map #(str % "\n") checks))
               (name* res) "\n"))))))

;; ============================================================
;; The corpus driver
;; ============================================================

(defn- parse-corpus
  "Split a datadriven file into [directive expected] pairs."
  [text]
  (loop [lines (str/split-lines text), out []]
    (cond
      (empty? lines) out

      (or (str/blank? (first lines)) (str/starts-with? (first lines) "#"))
      (recur (rest lines) out)

      :else
      (let [directive (first lines)
            after (drop-while #(not= "----" %) (rest lines))
            body (take-while #(not (str/blank? %)) (rest after))
            remaining (drop (+ 1 (count body)) after)]
        (recur remaining (conj out [directive (str/join "\n" body)]))))))

(defn- check-file [f]
  (let [cases (parse-corpus (slurp (io/resource (str "etcd-raft/quorum/" f))))]
    (is (pos? (count cases)) (str f " should contain cases"))
    (doseq [[directive expected] cases]
      (is (= expected (str/trimr (run-directive directive)))
          (str f ": " directive)))
    (count cases)))

(deftest majority-commit-corpus
  (testing "quorum/testdata/majority_commit.txt"
    (is (= 16 (check-file "majority_commit.txt")))))

(deftest majority-vote-corpus
  (testing "quorum/testdata/majority_vote.txt"
    (is (= 22 (check-file "majority_vote.txt")))))

(deftest joint-commit-corpus
  (testing "quorum/testdata/joint_commit.txt"
    (is (= 50 (check-file "joint_commit.txt")))))

(deftest joint-vote-corpus
  (testing "quorum/testdata/joint_vote.txt"
    (is (= 39 (check-file "joint_vote.txt")))))

;; ============================================================
;; The same arithmetic, expressed through the Membership protocol
;; ============================================================

(deftest committed-index-agrees-with-the-membership-predicate
  (testing "the k-th-largest formulation and the quorum? predicate agree

           This is the interesting question for the protocol, not for Raft:
           `Membership/quorum?` takes a PREDICATE over statements, while a Raft
           commit index is a QUANTILE. The two coincide -- the commit index is
           the largest N for which `(>= match N)` holds across a quorum -- but
           only by searching candidate values of N, which is why the direct
           k-th-largest computation is the one Raft actually uses."
    (let [ids [:a :b :c :d :e]
          membership node/cft-membership
          via-predicate
          (fn [acked]
            ;; Statements must IDENTIFY THEIR SENDER. Passing bare match
            ;; indexes -- where position encodes identity -- used to work only
            ;; because `quorum?` counted statements rather than distinct
            ;; senders, which was a safety hole: three copies of one
            ;; validator's vote cleared a quorum of four. Closing that hole
            ;; exposed this misuse, which is the more useful finding: a Raft
            ;; commit index is a QUANTILE over per-peer values, not a quorum
            ;; predicate over attributable statements, and only coincides with
            ;; one when each value is tagged with the peer it came from.
            (let [matches (map (fn [id] {:from id :match (get acked id 0)}) ids)
                  state {:validators ids}]
              (->> (cons 0 (distinct (map :match matches)))
                   (filter #(node/quorum?
                             membership state matches
                             (fn [s] (>= (:match s) %))))
                   (reduce max 0))))]
      (doseq [acked [{}
                     {:a 5}
                     {:a 5 :b 5 :c 5}
                     {:a 1 :b 2 :c 3 :d 4 :e 5}
                     {:a 9 :b 9 :c 1}
                     {:a 100 :b 101 :c 103 :d 103 :e 7}]]
        (is (= (long (raft/committed-index ids acked)) (via-predicate acked))
            (str "acked " acked))))))
