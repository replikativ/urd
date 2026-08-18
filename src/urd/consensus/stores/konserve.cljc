(ns urd.consensus.stores.konserve
  "A `DurableStore` on konserve.

  ## Why konserve's append log rather than a key per write

  `konserve.core/append` writes the element and a pointer and nothing else,
  which is what a write-ahead log wants: the cost of landing a record does not
  grow with the number of records already landed. `reduce-log` folds it back on
  restart. Both views the protocol owes a restarting node come from that one
  log -- the ordered records directly, and the merged map as a fold -- so there
  is no second key to keep in step with it.

  ## Writes are serialized, and this is not paranoia

  `append` is a read-modify-write on the list pointer, so two in flight against
  the same key interleave. The runtime issues writes from its event loop
  without awaiting the non-durable ones, so two CAN be in flight. Every write
  therefore goes through a single go-loop, one at a time.

  Measured rather than assumed. Removing the writer and appending directly,
  forty writes issued without awaiting came back in the order

      4 2 9 10 11 7 14 13 15 16 18 19 17 21 22 24 3 25 23 5 0 6 1 30 ...

  All forty records were still there -- this is not, at least against the
  in-memory store, a loss bug. It is an ORDERING bug, and that is bad enough
  twice over. `truncate-from` replay depends on log order being issue order:
  records applied out of order resurrect entries a later truncation dropped.
  And the merged view is a fold over the log, so it takes its value from
  whichever write happens to land last -- in that run `{:n 35}` where the node
  had written `{:n 39}`. A restarting Raft would come back with a stale term
  it never held.

  ## Portability

  This wraps a store you have already connected rather than connecting one, so
  it works against a filestore on the JVM and IndexedDB in the browser without
  this namespace knowing which. `connect-fs-store!` below is a JVM convenience,
  not the seam.

  Note that `konserve.filestore` fsyncs every blob by default
  (`:sync-blob? true`), so a record marked `:durable? false` is still written
  through to disk here. That is stronger than asked for, never weaker, and the
  distinction that survives is the one the runtime acts on: a durable write's
  gated effects wait for the disk and a buffered one's do not."
  (:require [konserve.core :as k]
            [urd.consensus.store :as store]
            #?(:clj [konserve.filestore :as fs])
            #?(:clj  [clojure.core.async :refer [chan go go-loop close! put! <!]]
               :cljs [clojure.core.async :refer [chan go go-loop close! put! <!]])
            [superv.async :refer [go-try- <?-]]))

(def default-log-key
  "Where the write log lives. Namespaced so a store shared with an application
  -- datahike on the same konserve, say -- cannot collide with it."
  ::write-log)

(def manifest-key
  "Where the CURRENT log key is recorded.

  Compaction cannot rewrite a log in place -- konserve's append log is a linked
  chain of separate store keys -- so a checkpoint writes a fresh log and then
  flips this one pointer. That flip is the atomic moment: a node that dies
  before it comes back reading the old log, a node that dies after comes back
  reading the new one, and neither can see a mixture."
  ::manifest)

(defn- resolve-key!
  "The log key this store is actually using, reading the manifest once.

  Lazy rather than resolved in the constructor, and that is a portability
  requirement rather than a preference: reading konserve is asynchronous on
  both platforms, `konserve-store` returns a store synchronously, and blocking
  to bridge the two works only on the JVM. Every caller here is already inside
  a go block, so resolving on first use costs nothing.

  A store that has been checkpointed names its own current log; reading the
  default after a checkpoint would silently restore from an empty one."
  [ks key-atom fallback]
  (go-try-
   (let [k @key-atom]
     (if (= ::unresolved k)
       (let [found (or (:log-key (<?- (k/get-in ks [manifest-key]))) fallback)]
         (compare-and-set! key-atom ::unresolved found)
         @key-atom)
       k))))

(defn- run-writer
  "One writer, forever. Serializes appends; see the namespace docstring."
  [ks log-key fallback-key queue]
  (go-loop []
    (when-let [[record reply] (<! queue)]
      ;; DEREFERENCED per record, not captured once: a checkpoint replaces the
      ;; log key underneath this loop, and an append that kept writing to the
      ;; old key would land in a log nothing reads.
      (let [result (<! (go-try- (<?- (k/append ks (<?- (resolve-key! ks log-key fallback-key))
                                               record))
                                true))]
        ;; The append's outcome is reported to the caller rather than logged
        ;; and swallowed. A `write!` that cannot say it failed is a barrier
        ;; that cannot be trusted.
        (put! reply (if (instance? #?(:clj Throwable :cljs js/Error) result)
                      result
                      true))
        (close! reply))
      (recur))))

(defrecord KonserveStore [ks log-key fallback queue]
  store/DurableStore

  (write! [_ record]
    (let [reply (chan 1)]
      (put! queue [record reply])
      reply))

  (fold [_ f init]
    ;; A straight pass-through: `k/reduce-log` already streams the log with an
    ;; accumulator and never builds the vector. That is the whole of the
    ;; bounded-heap fix on this backend -- konserve had the primitive and urd
    ;; was not using it, folding into `conj []` and handing the result on.
    (go-try- (<?- (k/reduce-log ks (<?- (resolve-key! ks log-key fallback))
                                f init))))

  (restore [this] (store/restore-via-fold this))

  (checkpoint! [_ records]
    (go-try-
     (let [old-key (<?- (resolve-key! ks log-key fallback))
           new-key (keyword (namespace ::manifest)
                            (str "write-log-" (System/currentTimeMillis)))]
       ;; Write the whole new log FIRST, while the manifest still names the old
       ;; one. Nothing reads `new-key` until the pointer moves, so a crash here
       ;; leaves an orphan the sweep can collect and a node that comes back on
       ;; the old log -- correct, merely uncompacted.
       (doseq [r records]
         (<?- (k/append ks new-key r)))
       ;; THE atomic moment.
       (<?- (k/assoc-in ks [manifest-key] {:log-key new-key}))
       (reset! log-key new-key)
       ;; Only now is the old log unreachable. Dissoc'ing it before the flip
       ;; would open a window in which a crash left the manifest pointing at a
       ;; log that had been swept.
       (<?- (k/dissoc ks old-key))
       true)))

  (close-store! [_]
    (close! queue)
    (go true)))

(defn konserve-store
  "Wrap a connected konserve store `ks`.

  Options: `:log-key` to place the write log somewhere other than the default.

  The konserve store is NOT closed by `close-store!` -- it may be shared with
  an application, and closing something you were lent is not yours to do."
  ([ks] (konserve-store ks {}))
  ([ks {:keys [log-key] :or {log-key default-log-key}}]
   (let [queue (chan 64)
         key-atom (atom ::unresolved)]
     (run-writer ks key-atom log-key queue)
     (->KonserveStore ks key-atom log-key queue))))

#?(:clj
   (defn connect-fs-store!
     "Connect a filestore at `path` and wrap it. JVM convenience.

     Synchronous, because it belongs in start-up rather than in a go block."
     ([path] (connect-fs-store! path {}))
     ([path opts]
      (konserve-store (fs/connect-fs-store path :opts {:sync? true}) opts))))
