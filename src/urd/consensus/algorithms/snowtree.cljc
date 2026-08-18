(ns urd.consensus.algorithms.snowtree
  "The Snowball Tree: what avalanchego actually runs under Snowman.

  `snow/consensus/snowball/tree.go`. A patricia trie over the BITS of the
  candidate ids, deciding the winner one bit-range at a time rather than
  deciding among the candidates as a set.

  ## Why this exists and the flat form does not suffice

  `Flat.RecordPoll` (`flat.go:29-33`) is three lines:

      pollMode, numVotes := votes.Mode()
      f.Nnary.RecordPoll(numVotes, pollMode)

  The plurality choice and its count, fed to one n-ary instance. That is what
  urd's Snowman did, exactly, and `NewFlat` has no non-test caller anywhere in
  avalanchego.

  The Tree instead feeds each node `votes.Len()` -- EVERY vote that reached it,
  whatever choice it names. So votes for two siblings COMBINE at every node
  above the bit where their ids diverge. Three children X, Y, Z where Y and Z
  share a leading bit that X does not: a 2/2 split between Y and Z still
  delivers 4 votes to the not-X side of the top binary node. The flat form sees
  a plurality of 2 and may not clear alpha at all. This is a real behavioural
  difference, not a change of representation, and it is why the reference can
  make progress on a contested slot that the flat form stalls on.

  ## Bit order

  avalanchego indexes bit `i` as bit `i mod 8` of byte `i div 8`, least
  significant first (`ids/id.go:140-155`). We index bit `i` as bit `i mod 4` of
  hex digit `i div 4`, least significant first.

  The difference is immaterial and worth saying why, because it looks like the
  kind of thing that would matter. The Tree is defined over an arbitrary but
  FIXED total order on the bits of an id; any such order gives the same
  algorithm. What changes is which pairs of ids happen to share a prefix, and
  since ids here are `hasch/uuid` digests that is uniformly random under either
  order. What we give up is the ability to replay avalanchego's own test
  vectors, which are literal `ids.ID` byte arrays -- and those were never
  replayable anyway, since urd's choices are not 32-byte avalanche ids. The
  tests port the structural claims instead.

  ## What a node holds

      {:kind :unary
       :preference       key
       :decided-prefix   the first bit this node covers
       :common-prefix    one past the last bit it covers
       :snow             a unary instance
       :should-reset     bool
       :child            node or nil}

      {:kind :binary
       :preferences  [key-when-bit-0 key-when-bit-1]
       :bit          the bit index this node decides
       :snow         a binary instance
       :should-reset [bool bool]
       :children     [node-or-nil node-or-nil]}

  Keys are fixed-width lowercase hex strings. The tree carries `:choices`, from
  key back to whatever the caller called a choice, so a caller keeps using its
  own ids and never sees a digest."
  (:require [urd.consensus.algorithms.snowflake :as sf]))

;; ============================================================
;; Bits over hex keys
;; ============================================================

(def ^:private hex-vals
  (zipmap "0123456789abcdef" (range 16)))

(defn- nibble [k i]
  (or (get hex-vals (nth k i))
      (throw (ex-info "snowtree keys must be lowercase hex" {:key k :at i}))))

(defn bit-at
  "Bit `i` of key `k`. See the namespace docstring on ordering."
  [k i]
  (bit-and 1 (bit-shift-right (nibble k (quot i 4)) (mod i 4))))

(defn num-bits [k] (* 4 (count k)))

(defn equal-subset?
  "Do `k1` and `k2` agree on every bit in [start, stop)?

  `ids/bits.go:21-65` does this with byte masks; a loop is the same relation and
  the widths here are 128 bits, reached only from `add`."
  [start stop k1 k2]
  (loop [i start]
    (cond
      (>= i stop) true
      (not= (bit-at k1 i) (bit-at k2 i)) false
      :else (recur (inc i)))))

(defn first-difference
  "The lowest index in [start, stop) at which `k1` and `k2` differ, or nil.
  `ids/bits.go:67-130`."
  [start stop k1 k2]
  (loop [i start]
    (cond
      (>= i stop) nil
      (not= (bit-at k1 i) (bit-at k2 i)) i
      :else (recur (inc i)))))

;; ============================================================
;; Bags
;;
;; A bag here is {key -> weight}. avalanchego's `bag.Bag[ids.ID]` is a multiset
;; and `Len` counts multiplicity; weight IS multiplicity, so `bag-len` is `Len`.
;; ============================================================

(defn- bag-len [b] (reduce + 0 (vals b)))

(defn- bag-filter [b pred]
  (into {} (filter (fn [[k _]] (pred k))) b))

;; ============================================================
;; Nodes
;; ============================================================

(declare node-add node-record-poll)

(defn- node-preference [n]
  (case (:kind n)
    :unary (:preference n)
    :binary (nth (:preferences n) (:preference (:snow n)))))

(defn- node-decided-prefix [n]
  (case (:kind n)
    :unary (:decided-prefix n)
    :binary (:bit n)))

(defn- node-finalized? [n]
  (sf/instance-finalized? (:snow n)))

(defn- unary-node [params preference decided-prefix common-prefix]
  {:kind :unary
   :preference preference
   :decided-prefix decided-prefix
   :common-prefix common-prefix
   :snow (sf/unary-snowflake params)
   :should-reset false
   :child nil})

;; ------------------------------------------------------------
;; Add
;; ------------------------------------------------------------

(defn- unary-add
  "`unaryNode.Add` (`tree.go:328-406`), including its five-case split.

  The case analysis is the heart of the structure and the comment block above
  it upstream is 100 lines of ASCII diagrams; the cases are named here in the
  same order."
  [u params choice]
  (if (node-finalized? u)
    ;; Only reachable once the tree is decided, or at a leaf.
    u
    (let [{:keys [decided-prefix common-prefix preference]} u
          index (first-difference decided-prefix common-prefix preference choice)]
      (if (nil? index)
        ;; No difference in the range this node covers, so it does not split.
        ;; A child, if there is one, must be where the difference lives -- this
        ;; node finalizes before any child could, so the new choice matches our
        ;; prefix by construction.
        (cond-> u (:child u) (update :child node-add params choice))

        (let [bit (bit-at preference index)
              b {:kind :binary
                 :bit index
                 :snow (sf/unary-extend (:snow u) bit)
                 :should-reset [(:should-reset u) (:should-reset u)]
                 :preferences (assoc [nil nil] bit preference (- 1 bit) choice)
                 :children [nil nil]}
              new-child (unary-node params choice (inc index) (num-bits choice))]
          (cond
            ;; Case 2: this node was voting over exactly one bit.
            (= decided-prefix (dec common-prefix))
            (assoc b :children (cond-> (assoc [nil nil] bit (:child u))
                                 (:child u) (assoc (- 1 bit) new-child)))

            ;; Case 3: split on the first bit this node covers.
            (= index decided-prefix)
            (assoc b :children (-> (assoc [nil nil] bit (update u :decided-prefix inc))
                                   (assoc (- 1 bit) new-child)))

            ;; Case 4: split on the last bit this node covers.
            (= index (dec common-prefix))
            (let [b (assoc b :children (cond-> (assoc [nil nil] bit (:child u))
                                         (:child u) (assoc (- 1 bit) new-child)))]
              (assoc u :common-prefix (dec common-prefix) :child b))

            ;; Case 5: split on an interior bit. This node keeps the bits below
            ;; the split; a fresh copy of it takes the bits above.
            :else
            (let [b (assoc b :children (-> (assoc [nil nil] bit (assoc u :decided-prefix (inc index)))
                                           (assoc (- 1 bit) new-child)))]
              {:kind :unary
               :preference preference
               :decided-prefix decided-prefix
               :common-prefix index
               ;; `Clone()` upstream. Values here, so sharing is already safe.
               :snow (:snow u)
               :should-reset (:should-reset u)
               :child b})))))))

(defn- binary-add
  "`binaryNode.Add` (`tree.go:496-509`)."
  [b params choice]
  (let [bit (bit-at choice (:bit b))]
    (if-let [child (nth (:children b) bit)]
      (assoc-in b [:children bit] (node-add child params choice))
      ;; A nil child means either the choice is already in the tree, or a
      ;; previous decision rejected the branch it would sit on. Both are no-ops.
      b)))

(defn- node-add [n params choice]
  (case (:kind n)
    :unary (unary-add n params choice)
    :binary (binary-add n params choice)))

;; ------------------------------------------------------------
;; RecordPoll
;; ------------------------------------------------------------

(defn- unary-record-poll
  "`unaryNode.RecordPoll` (`tree.go:408-449`). Returns [node successful?]."
  [u params votes reset?]
  (let [u (cond-> u
            reset? (-> (update :snow sf/unary-record-unsuccessful-poll)
                       (assoc :should-reset true)))
        n-votes (bag-len votes)]
    (if (< n-votes (:alpha-preference params))
      [(-> u
           (update :snow sf/unary-record-unsuccessful-poll)
           (assoc :should-reset true))
       false]
      ;; The alpha check lives HERE, not in the unary instance -- see
      ;; `snowflake/unary-record-poll`.
      (let [u (update u :snow sf/unary-record-poll n-votes)]
        (if-let [child (:child u)]
          ;; Votes pass down unfiltered: a unary node covers a run of bits on
          ;; which, by construction, every id in the tree already agrees.
          (let [[new-child _] (node-record-poll child params votes (:should-reset u))]
            (if (node-finalized? u)
              ;; Decided, so collapse: this node's job is done and its child
              ;; takes its place.
              [new-child true]
              [(-> u
                   ;; Upstream reads `u.child.Preference()` here without
                   ;; assigning `newChild`, which is safe only under the
                   ;; invariant that a child cannot finalize before its parent
                   ;; (identical vote counts, so identical confidence). We
                   ;; assign: a no-op under that invariant, and not a landmine
                   ;; if it ever fails to hold.
                   (assoc :child new-child)
                   (assoc :preference (node-preference new-child))
                   (assoc :should-reset false))
               true]))
          [(assoc u :should-reset false) true])))))

(defn- binary-record-poll
  "`binaryNode.RecordPoll` (`tree.go:512-552`). Returns [node successful?]."
  [b params votes reset?]
  (let [bit-of (fn [k] (bit-at k (:bit b)))
        ones (bag-filter votes #(= 1 (bit-of %)))
        zeros (bag-filter votes #(= 0 (bit-of %)))
        ;; Which side is even in contention. Only a side that clears alpha can
        ;; win, so the zero side is the default.
        bit (if (>= (bag-len ones) (:alpha-preference params)) 1 0)
        pruned (if (= 1 bit) ones zeros)
        b (cond-> b
            reset? (-> (update :snow sf/binary-record-unsuccessful-poll)
                       (assoc-in [:should-reset bit] true)))
        ;; The losing side did not get the votes, whatever else happened.
        b (assoc-in b [:should-reset (- 1 bit)] true)
        n-votes (bag-len pruned)]
    (if (< n-votes (:alpha-preference params))
      [(-> b
           (update :snow sf/binary-record-unsuccessful-poll)
           (assoc-in [:should-reset bit] true))
       false]
      (let [b (update b :snow sf/binary-record-poll n-votes bit)]
        (if-let [child (nth (:children b) bit)]
          (let [[new-child _] (node-record-poll child params pruned
                                                (nth (:should-reset b) bit))]
            (if (node-finalized? b)
              ;; Decided, and it must have been decided on `bit` by this very
              ;; poll, so the winning child replaces us.
              [new-child true]
              [(-> b
                   (assoc-in [:children bit] new-child)
                   (assoc-in [:preferences bit] (node-preference new-child))
                   (assoc-in [:should-reset bit] false))
               true]))
          [(assoc-in b [:should-reset bit] false) true])))))

(defn- node-record-poll [n params votes reset?]
  (case (:kind n)
    :unary (unary-record-poll n params votes reset?)
    :binary (binary-record-poll n params votes reset?)))

;; ============================================================
;; The Tree
;; ============================================================

(defn tree
  "A fresh Tree preferring `choice`, whose bit key is `key`.

  The root is a unary node spanning the whole key: with one choice there is
  nothing to conflict on yet (`tree.go:20-32`)."
  [params choice key]
  {:params params
   :choices {key choice}
   :keys {choice key}
   :should-reset false
   :node (unary-node params key 0 (num-bits key))})

(defn tree-add
  "`Tree.Add` (`tree.go:59-65`). Adding a choice already decided AGAINST -- one
  whose key disagrees with the preference somewhere in the settled prefix -- is
  a no-op, which is how a rejected branch stays rejected."
  [t choice key]
  (let [prefix (node-decided-prefix (:node t))]
    (if (equal-subset? 0 prefix (node-preference (:node t)) key)
      (-> t
          (assoc-in [:choices key] choice)
          (assoc-in [:keys choice] key)
          (update :node node-add (:params t) key))
      t)))

(defn tree-record-poll
  "`Tree.RecordPoll` (`tree.go:67-87`). `votes` is {choice -> weight}.

  Votes for a branch the settled prefix has already rejected are dropped before
  anything sees them."
  [t votes]
  (let [by-key (reduce-kv (fn [m choice w]
                            (if-let [k (get (:keys t) choice)]
                              (assoc m k w)
                              m))
                          {}
                          votes)
        decided (node-decided-prefix (:node t))
        preference (node-preference (:node t))
        filtered (bag-filter by-key #(equal-subset? 0 decided preference %))
        [node _] (node-record-poll (:node t) (:params t) filtered (:should-reset t))]
    (assoc t :node node :should-reset false)))

(defn tree-record-unsuccessful-poll
  "`Tree.RecordUnsuccessfulPoll`: lazy. The reset is handed to the nodes on the
  next poll rather than walked into them now."
  [t]
  (assoc t :should-reset true))

(defn tree-preference [t]
  (get (:choices t) (node-preference (:node t))))

(defn tree-finalized? [t]
  (node-finalized? (:node t)))

(defn describe
  "A nested summary of the trie, for tests and for reading a failure.

  `Printable` upstream (`tree.go:190-200`, `:556-565`). Structure is what is
  being ported here, so some tests assert on it directly rather than only on
  behaviour."
  [t]
  (letfn [(go [n]
              (case (:kind n)
                :unary (cond-> {:unary [(:decided-prefix n) (:common-prefix n)]
                                :confidence (:confidence (:snow n))
                                :finalized? (:finalized? (:snow n))}
                         (:child n) (assoc :child (go (:child n))))
                :binary (cond-> {:binary (:bit n)
                                 :confidence (:confidence (:snow n))
                                 :prefers (:preference (:snow n))
                                 :finalized? (:finalized? (:snow n))}
                          (some some? (:children n))
                          (assoc :children (mapv #(some-> % go) (:children n))))))]
    (go (:node t))))
