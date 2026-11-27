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
  "Legacy shared checkpoint manifest. Its :log-key identifies a physical log,
  but older releases did not record which configured log owned it."
  ::manifest)

(defn- scoped-manifest [logical-key]
  [manifest-key logical-key])

(defn- resolve-key!
  "Resolve a logical log once, in the same queue that orders its operations."
  [ks key-atom logical-key]
  (go-try-
   (if (= ::unresolved @key-atom)
     (let [scoped (scoped-manifest logical-key)
           current (<?- (k/get-in ks [scoped]))
           legacy (when-not current (<?- (k/get-in ks [manifest-key])))
           legacy-key (:log-key legacy)
           physical-key
           (cond
             current (or (:log-key current)
                         (throw (ex-info "Invalid consensus log manifest" {:manifest scoped})))
             (nil? legacy) logical-key
             (nil? legacy-key) (throw (ex-info "Invalid legacy consensus manifest"
                                               {:manifest manifest-key}))
             (= logical-key default-log-key) legacy-key
             :else (throw
                    (ex-info
                     (str "Legacy consensus manifest has no owner. Stop writers and inspect "
                          "the legacy and requested logs. Copy the verified history into "
                          "a private log, then set the scoped manifest to {:log-key private-log-key}.")
                     {:requested-log logical-key :legacy-log legacy-key :manifest scoped})))]
       (reset! key-atom physical-key))
     @key-atom)))

(defn- replace-log! [ks key-atom logical-key old-key records]
  (go-try-
   (let [new-key (keyword (namespace ::manifest) (str "write-log-" (random-uuid)))
         ;; A legacy manifest may be the only way to recover an unidentified
         ;; custom log. Preserve that source across the first scoped checkpoint.
         legacy-key (:log-key (<?- (k/get-in ks [manifest-key])))]
     (doseq [record records]
       (<?- (k/append ks new-key record)))
     (<?- (k/assoc-in ks [(scoped-manifest logical-key)] {:log-key new-key}))
     (reset! key-atom new-key)
     (when (not= old-key legacy-key)
       (<?- (k/dissoc ks old-key)))
     true)))

(defn- run-writer [ks log-key fallback queue]
  (go-loop []
    (if-let [[operation reply] (<! queue)]
      (let [result (<! (go-try-
                        (let [key (<?- (resolve-key! ks log-key fallback))]
                          (<?- (operation key)))))]
        (when (some? result) (put! reply result))
        (close! reply)
        (recur))
      true)))

(defn- submit! [queue operation]
  (let [reply (chan 1)]
    (put! queue [operation reply]
          (fn [accepted?]
            (when-not accepted?
              (put! reply (ex-info "Consensus store is closed" {}))
              (close! reply))))
    reply))

(defrecord KonserveStore [ks log-key logical-key queue writer]
  store/DurableStore

  (write! [_ record]
    (submit! queue (fn [key] (go-try- (<?- (k/append ks key record)) true))))

  (fold [_ f init]
    (submit! queue (fn [key] (k/reduce-log ks key f init))))

  (restore [this] (store/restore-via-fold this))

  (checkpoint! [_ records]
    (submit! queue (fn [key] (replace-log! ks log-key logical-key key records))))

  (close-store! [_]
    (close! queue)
    writer))

(defn konserve-store
  "Wrap a connected konserve store `ks`.

  Options: `:log-key` to place the write log somewhere other than the default.

  The konserve store is NOT closed by `close-store!` -- it may be shared with
  an application, and closing something you were lent is not yours to do."
  ([ks] (konserve-store ks {}))
  ([ks {:keys [log-key] :or {log-key default-log-key}}]
   (let [queue (chan 64)
         key-atom (atom ::unresolved)
         writer (run-writer ks key-atom log-key queue)]
     (->KonserveStore ks key-atom log-key queue writer))))

#?(:clj
   (defn connect-fs-store!
     "Connect a filestore at `path` and wrap it. JVM convenience.

     Synchronous, because it belongs in start-up rather than in a go block."
     ([path] (connect-fs-store! path {}))
     ([path opts]
      (konserve-store (fs/connect-fs-store path :opts {:sync? true}) opts))))
