(ns urd.konserve-checkpoint-test
  (:require [cljs.test :refer-macros [async deftest is]]
            [cljs.core.async :refer [<!]]
            [konserve.memory :as memory]
            [urd.consensus.store :as store]
            [urd.consensus.stores.konserve :as backend])
  (:require-macros [cljs.core.async.macros :refer [go]]))

(deftest checkpoint-and-tail-survive-reopen
  (async done
         (go
           (let [ks (<! (memory/new-mem-store))
                 s (backend/konserve-store ks)
                 checkpoint {:writes {:height 1}}
                 tail {:writes {:height 2}}
                 replace-log (store/checkpoint! s [checkpoint])
                 append (store/write! s tail)]
             (is (true? (<! replace-log)))
             (is (true? (<! append)))
             (<! (store/close-store! s))
             (let [reopened (backend/konserve-store ks)]
               (is (= [checkpoint tail] (:writes (<! (store/restore reopened)))))
               (<! (store/close-store! reopened))))
           (done))))
