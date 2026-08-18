(ns urd.consensus.pending
  "Park an input whose dependency we do not hold; re-process it when we do.

  ## The gap this closes

  Six reference audits found the same defect in four algorithms, and it is the
  single most common way this codebase strands a node:

  - round-robin answered a peer behind us with silence;
  - Bullshark drops a header whose parents are missing, fires one `:want`, and
    never revisits it -- so it never votes for that header even once the
    parents land;
  - Snowman drops a chit naming a block it does not hold, and nothing ever
    requests the block;
  - Tendermint keeps the first proposal it saw and cannot replace it, so a node
    holding a full quorum of precommits for a different value waits forever.

  Every one is the same shape: something arrived that REFERENCES what we lack,
  we could not use it, and we threw it away. The references all do the opposite
  and all in the same way -- avalanchego `SendGet`s the block and
  `blocked.Schedule`s the vote against it (`engine.go:709-722`, `:396-415`);
  Narwhal queues `WaiterMessage::SyncParents` carrying the header itself and
  loops it back through `process_header` (`header_waiter.rs:239-277`,
  `core.rs:644`); btcd parks the orphan, requests `GetOrphanRoot`, and
  reconsiders on arrival (`netsync/manager.go:788-794`).

  ## Why this is a helper and not a new effect

  The protocol already has everything needed. `send-to` asks the peer that
  referenced the thing -- the one peer we know has it -- and `deliver-self`
  hands a parked input back to the node at the next tick, which is exactly
  Narwhal's loop-back. What was missing was not a capability but the BOOKKEEPING
  between them, written once instead of four subtly different times.

  ## Generalised from the one that was already right

  Nakamoto's orphan pool does this correctly and was fuzzed over 60 random
  branch trees without stranding a node inside itself, so this is its shape
  rather than a fresh invention: park keyed by the DEPENDENCY, evict oldest by
  ARRIVAL SEQUENCE rather than by timestamp (whole-second clocks tie, and
  breaking a tie by id or by map order makes eviction arbitrary -- a header
  delivered child-first could evict its own parent one message later), and
  expire on age.

  One thing it does that Nakamoto did not: `park` is idempotent on the item id.
  btcd checks `if _, exists := b.orphans[hash]; exists` BEFORE adding
  (`process.go:162-166`); Nakamoto did not, so a re-delivered orphan re-ran
  eviction and re-stamped its arrival sequence -- measurably evicting a
  legitimate orphan to make room for something already held, and defeating the
  FIFO property the sequence counter exists to establish. Rotating through
  already-held headers kept the pool one below capacity indefinitely. Fixed
  here by construction, for every user.

  ## What this does NOT do

  It does not decide when to ask, whom to ask, or what a request looks like:
  those are the algorithm's, and differ. It holds inputs and hands them back."
  (:refer-clojure :exclude [empty]))

(def empty-pool
  "A pool holding nothing.

  `:seq` is a monotonic arrival counter and is never reset, so eviction order
  stays total even after the pool empties and refills."
  {:by-dep {} :items {} :meta {} :seq 0})

(defn held
  "How many inputs are parked."
  [pool]
  (count (:items pool)))

(defn waiting-on?
  "Is anything parked against `dep`?"
  [pool dep]
  (boolean (seq (get-in pool [:by-dep dep]))))

(defn parked?
  "Is this item already held? Callers that must not re-request should check."
  [pool id]
  (contains? (:items pool) id))

(defn park
  "Hold `item` (identified by `id`) until `dep` arrives.

  Idempotent on `id`: parking something already held changes nothing at all --
  not the arrival sequence, not the eviction order, not the pool size. See the
  namespace docstring for what re-stamping cost btcd's equivalent.

  `at` is whatever clock the algorithm keeps; it is compared only against the
  `now` passed to `reap`, and may be nil if the caller does not expire."
  [pool id dep item at]
  (if (parked? pool id)
    pool
    (-> pool
        (update-in [:by-dep dep] (fnil conj []) id)
        (assoc-in [:items id] item)
        (assoc-in [:meta id] {:seq (:seq pool) :at at :dep dep})
        (update :seq inc))))

(defn- forget [pool id]
  (let [dep (get-in pool [:meta id :dep])
        remaining (vec (remove #(= id %) (get-in pool [:by-dep dep])))]
    (-> pool
        (update :by-dep (fn [m] (if (seq remaining) (assoc m dep remaining) (dissoc m dep))))
        (update :items dissoc id)
        (update :meta dissoc id))))

(defn release
  "Take everything parked on `dep`. Returns `[pool' items]`.

  Items come back in ARRIVAL order, so an algorithm that parked a chain of
  dependents re-processes them in the order it received them. Releasing a
  dependency nothing waited on is not an error and returns no items."
  [pool dep]
  (let [ids (get-in pool [:by-dep dep] [])
        items (mapv #(get-in pool [:items %]) ids)]
    [(reduce forget pool ids) items]))

(defn reap
  "Drop what has waited too long, then evict oldest-first down to `limit`.

  Returns `[pool' dropped-count]`. A parked input is a bet that its dependency
  is coming; both bounds exist because an unbounded pool is a memory leak an
  adversary can drive, and neither is a substitute for the other -- expiry
  bounds how long junk lingers, the limit bounds how much of it there can be at
  once.

  `ttl` or `now` being nil skips expiry; `limit` being nil skips eviction."
  [pool now ttl limit]
  (let [expired (if (and now ttl)
                  (keep (fn [[id {:keys [at]}]]
                          (when (and at (> (- now at) ttl)) id))
                        (:meta pool))
                  [])
        pool (reduce forget pool expired)
        over (if limit (max 0 (- (held pool) limit)) 0)
        ;; Oldest by arrival sequence. See the namespace docstring on why this
        ;; is not by timestamp.
        evicted (->> (:meta pool)
                     (sort-by (comp :seq val))
                     (take over)
                     (mapv key))]
    [(reduce forget pool evicted) (+ (count expired) (count evicted))]))

(defn deps
  "Every dependency currently being waited on. What to re-request."
  [pool]
  (vec (keys (:by-dep pool))))
