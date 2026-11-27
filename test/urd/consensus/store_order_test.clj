(ns urd.consensus.store-order-test
  (:require [clojure.core.async :as async :refer [<!!]]
            [clojure.test :refer [deftest is]]
            [konserve.core :as k]
            [konserve.memory :as memory]
            [urd.consensus.store :as store]
            [urd.consensus.stores.konserve :as backend]))

(deftest restore-issues-the-fold-before-returning
  (let [issued-on (atom nil)
        reply (async/promise-chan)
        backend (reify store/DurableStore
                  (fold [_ _ _]
                    (reset! issued-on (Thread/currentThread))
                    reply))
        pending (store/restore-via-fold backend)]
    (is (identical? (Thread/currentThread) @issued-on))
    (async/put! reply [{:writes {:height 3}}])
    (is (= {:durable {:height 3} :writes [{:writes {:height 3}}]} (<!! pending)))))

(deftest a-pending-read-precedes-a-later-checkpoint
  (doseq [s [(store/memory-store)
             (backend/konserve-store (<!! (memory/new-mem-store)))]]
    (let [before {:writes {:height 1}}
          after {:writes {:height 2}}
          append (store/write! s before)
          fold (store/fold s conj [])
          restore (store/restore s)
          checkpoint (store/checkpoint! s [after])]
      (is (true? (<!! append)))
      (is (= [before] (<!! fold)))
      (is (= [before] (:writes (<!! restore))))
      (is (true? (<!! checkpoint)))
      (is (= [after] (:writes (<!! (store/restore s)))))
      (<!! (store/close-store! s)))))

(deftest independently-checkpointed-logs-reopen-by-name
  (let [ks (<!! (memory/new-mem-store))
        open #(backend/konserve-store ks {:log-key %})
        ids [backend/default-log-key :custom-a :custom-b]
        stores (mapv open ids)]
    (doseq [[s id] (map vector stores ids)]
      (is (true? (<!! (store/checkpoint! s [{:writes {:owner id}}]))))
      (is (true? (<!! (store/write! s {:writes {:tail id}}))))
      (<!! (store/close-store! s)))
    (doseq [id ids]
      (let [s (open id)]
        (is (= {:owner id :tail id} (:durable (<!! (store/restore s)))))
        (<!! (store/close-store! s))))))

(deftest ambiguous-legacy-custom-log-requires-explicit-recovery
  (let [ks (<!! (memory/new-mem-store))
        old {:writes {:height 7}}
        current {:writes {:height 8}}
        open-custom #(backend/konserve-store ks {:log-key :audit})
        legacy-key :preexisting-compacted-log
        error-data (fn []
                     (let [s (open-custom)
                           error (<!! (store/restore s))]
                       (<!! (store/close-store! s))
                       (is (instance? clojure.lang.ExceptionInfo error))
                       (ex-data error)))]
    (<!! (k/append ks legacy-key old))
    (<!! (k/assoc-in ks [backend/manifest-key] {:log-key legacy-key}))
    (let [s (backend/konserve-store ks)
          {:keys [manifest]} (error-data)]
      (is (= [old] (:writes (<!! (store/restore s)))))
      (is (true? (<!! (store/checkpoint! s [current]))))
      (<!! (store/close-store! s))
      (is (= {:requested-log :audit :legacy-log legacy-key :manifest manifest} (error-data)))
      (is (= [old] (<!! (k/reduce-log ks legacy-key conj []))))
      (let [reopened (backend/konserve-store ks)]
        (is (= [current] (:writes (<!! (store/restore reopened)))))
        (<!! (store/close-store! reopened)))
      ;; Complete the documented recovery with a separately verified copy.
      (<!! (k/append ks :verified-private-log old))
      (<!! (k/assoc-in ks [manifest] {:log-key :verified-private-log}))
      (let [s (open-custom)]
        (is (= [old] (:writes (<!! (store/restore s)))))
        (<!! (store/close-store! s))))))
