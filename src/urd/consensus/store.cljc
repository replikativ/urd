(ns urd.consensus.store
  "Durable storage behind the `persist-then` effect.

  ## What a store is responsible for, and what it is not

  Very little, deliberately. A store lands write RECORDS in order and hands
  them back on restart. It never interprets a key.

  That division is forced by the shape of what the algorithms write. Look at
  the six of them together and `:writes` carries three different disciplines
  under one map:

  - **snapshot**, overwrite the key -- Raft's `:hard-state`, SCP's `:scp`,
    Tendermint's `:last-signed`;
  - **append**, extend a log -- Raft's `:entries`, Tendermint's `:wal`;
  - **content-keyed put** -- Bullshark's `[:cert id]`, Nakamoto's
    `[:header id]`.

  A store that tried to honour all three would need to know which keys mean
  what, which is to say it would need a copy of each algorithm's storage
  schema. So it knows none of them. It keeps the ordered log; the ALGORITHM
  replays it in `init` and decides what a key means. `truncate-from` rides
  along as replay metadata rather than as an instruction to truncate anything
  here -- an append log cannot un-append, and a merged map cannot express a
  truncation at all.

  This is the simulator's contract, stated as a protocol. `sim/restart` hands a
  node `{:durable <merge of every landed write> :writes <ordered records>}` and
  the same two views appear here, so an algorithm's restart path cannot tell
  the interpreters apart -- which is the property the whole two-interpreter
  design rests on.

  ## `:durable` is derived, not stored

  The merged view is a fold over the log rather than a second key kept in step
  with it. Two keys would have to be written together and could not be, so
  every crash between them would leave a snapshot disagreeing with the log it
  summarises -- and the disagreement would surface only on the restart path,
  which is the one path that is hard to test and where being wrong is worst.
  One key has no such window.

  ## What is NOT here

  Compaction. The log grows without bound, so a node that runs long enough
  restarts slowly and eventually not at all. The simulator has the same
  property and neither has needed a snapshot-and-truncate cycle yet. It is a
  real bound, and it is written down rather than discovered later: nothing in
  this namespace should be read as claiming a store you can leave running for a
  year."
  (:require #?(:clj  [clojure.core.async :refer [go]]
               :cljs [clojure.core.async :refer [go]])
            [superv.async :refer [go-try- <?-]]))

(defprotocol DurableStore
  "Where `persist-then` writes land."

  (write! [this record]
    "Land one record: `{:writes {k v} :durable? bool :truncate-from idx}`.

     Returns a channel yielding true once the record SURVIVES A CRASH. A store
     that returns before that has not implemented this protocol, it has
     implemented a faster one -- the barrier is the only thing `persist-then`
     buys and a premature completion silently removes it.")

  (fold [this f init]
    "Stream every landed record through `f`, OLDEST FIRST, and yield the
     accumulator on a channel.

     The bounded-heap primitive. `restore` materialises the whole log into a
     vector before an algorithm sees any of it, so both memory and restart time
     grow with total history -- for a node that has been up for a week, the
     write log IS the history. `fold` never holds more than one record plus
     whatever the algorithm chose to keep.

     `f` is `(fn [acc record] acc')` and must be pure and synchronous: it runs
     once per record on whatever thread the store is draining on, so a `f` that
     parks would stall the drain, and one that throws aborts the fold.

     Backends implement THIS; `restore` has a derived default below, so no
     existing algorithm changes and each can move over when it is worth it.")

  (restore [this]
    "Everything that landed before now.

     Returns a channel yielding `{:durable <merged map> :writes <ordered
     vector of records>}`, the two views `sim/restart` supplies. Empty maps and
     vectors for a fresh node, never nil.

     Defined in terms of `fold`, and deliberately the UNBOUNDED one: it exists
     so algorithms that have not moved to `fold` keep working unchanged. An
     algorithm that only needs a merged view, or that folds the log into its
     own state as SCP and Tendermint do, should call `fold` and never build
     this vector at all.")

  (checkpoint! [this records]
    "Replace the durable log with exactly `records`. Returns a channel of true.

     The compaction primitive. `fold` bounds the HEAP; this bounds the LOG, and
     without it a node that has been up for a week restarts by replaying a
     week -- the write log is the history.

     `records`, not state, and that is the whole design. The store has no idea
     what an algorithm's durable state means, and giving it one would put a
     second interpretation of every write in a place that cannot be tested
     against the first. So the ALGORITHM supplies a short list of records that
     folds to the same state it would have reached by replaying everything, and
     `fold`'s contract is untouched: it still yields records, oldest first, and
     no algorithm that has not opted in changes at all.

     Retention is the caller's too: an algorithm that wants etcd's
     `SnapshotCatchUpEntries` behaviour includes the recent raw records in
     `records` after its summary. That is deliberate -- etcd's own comment
     explains that compacting all the way to the head means any peer one entry
     behind needs a snapshot, and since sending one is slow you compact again
     meanwhile, which is a self-reinforcing cycle. Only the algorithm knows how
     far behind a peer it still wants to serve.

     MUST be atomic with respect to a crash: a node that dies during a
     checkpoint comes back holding either the old log or the new one, never a
     mixture and never nothing.")

  (close-store! [this]
    "Release resources. Returns a channel that completes when closed."))

(defn merge-durable
  "Fold write records into the merged view: last write wins per key.

  Shared by every implementation so the two views cannot drift apart in one
  store and not another."
  [records]
  (reduce (fn [m r] (merge m (:writes r))) {} records))

;; ============================================================
;; In-memory
;; ============================================================

(defn restore-via-fold
  "`restore` in terms of `fold`, so a backend implements one method.

  This is the unbounded path by construction -- it accumulates every record
  into a vector and then merges it -- and that is the point: it keeps every
  algorithm that has not moved to `fold` working exactly as before, rather
  than making a heap fix into a rewrite of seven state machines."
  [store]
  (go-try-
   (let [records (<?- (fold store conj []))]
     {:durable (merge-durable records) :writes records})))

(defrecord MemoryStore [state]
  DurableStore

  (write! [_ record]
    (swap! state conj record)
    (go true))

  (fold [_ f init]
    (go (reduce f init @state)))

  (restore [this] (restore-via-fold this))

  (checkpoint! [_ records]
    ;; Atomic by construction: one `reset!` of one atom.
    (reset! state (vec records))
    (go true))

  (close-store! [_] (go true)))

(defn memory-store
  "A store that keeps records in an atom.

  Durable with respect to a node restart and not with respect to a process
  one, which is exactly the crash model the simulator uses: hand the same
  store to a fresh runtime and the node comes back with what it had written.
  That makes it the right store for restart TESTS, and the wrong one for
  anything that has to survive the JVM.

  Pass `:records` to start from a prior log -- a restart from a state you
  constructed rather than one you had to drive a node into."
  ([] (memory-store {}))
  ([{:keys [records] :or {records []}}]
   (->MemoryStore (atom (vec records)))))

(defn records
  "The raw landed records of a `memory-store`. For assertions."
  [store]
  @(:state store))
