(ns urd.consensus.raft-disk-recovery-test
  (:require [clojure.core.async :refer [<!!]]
            [clojure.test :refer [deftest is]]
            [konserve.core :as k]
            [konserve.filestore :as fs]
            [urd.consensus.algorithms.raft :as raft]
            [urd.consensus.networks.simulation :as net]
            [urd.consensus.node :as n]
            [urd.consensus.runtime :as rt]
            [urd.consensus.store :as store]
            [urd.consensus.stores.konserve :as disk])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(deftest ^:integration follower-reopens-a-checkpoint-ahead-of-its-application
  (let [dir (.toFile (Files/createTempDirectory "urd-raft-recovery" (make-array FileAttribute 0)))
        path (.getPath dir)
        entries (fn [indices] (mapv #(hash-map :index % :term 1 :data %) indices))
        open-backend #(fs/connect-fs-store path :opts {:sync? true})]
    (try
      ;; The application's transaction reached index 2 before shutdown. Raft
      ;; independently persisted a checkpoint with four committed entries.
      (let [ks (open-backend)
            wal (disk/konserve-store ks)]
        (k/assoc-in ks [:app] [1 2] {:sync? true})
        (is (true? (<!! (store/checkpoint! wal [{:writes {:entries (entries [1 2 3 4])
                                                          :hard-state {:term 1 :commit 4}}}]))))
        (<!! (store/close-store! wal)))
      (let [ks (open-backend)
            wal (disk/konserve-store ks)
            done (promise)
            runtime (<!! (rt/start-runtime!
                          {:peer-id :a :node (raft/make) :validators [:a :b :c]
                           :auth :none :tick-ms 60000 :store wal
                           :network (net/create-simulation-network :a (net/create-router))
                           :delivered-through #(count (k/get-in ks [:app] nil {:sync? true}))
                           :on-finalize (fn [batch]
                                          (let [ids (mapv :index batch)]
                                            (k/update-in ks [:app] #(into % ids) {:sync? true})
                                            (when (= 5 (peek ids)) (deliver done true))))}))]
        (try
          (rt/send-event! runtime (n/message-received :b {:type :heartbeat :term 1 :commit 4} #{:b}))
          (rt/send-event! runtime (n/message-received :b {:type :app :term 1 :commit 5
                                                          :prev-index 4 :prev-term 1
                                                          :entries (entries [5])} #{:b}))
          (is (= true (deref done 10000 nil)))
          (is (nil? (rt/last-error runtime)))
          (finally
            (<!! (rt/stop-runtime! runtime))
            (<!! (store/close-store! wal)))))
      (is (= [1 2 3 4 5] (k/get-in (open-backend) [:app] nil {:sync? true})))
      (finally (fs/delete-store path)))))
