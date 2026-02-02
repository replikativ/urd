;; Check if vote processing could be blocking

(require '[urd.log :as log])
(require '[konserve.memory :refer [new-mem-store]])  
(require '[clojure.core.async :refer [<!! go-loop <!]])

(println "Testing vote processing speed...")

(let [store (<!! (new-mem-store))
      validator-set {#uuid "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa" "pubkey-a"
                     #uuid "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb" "pubkey-b"
                     #uuid "cccccccc-cccc-cccc-cccc-cccccccccccc" "pubkey-c"}
      log (log/create-consensus-log store validator-set)
      proposal-id #uuid "dddddddd-dddd-dddd-dddd-dddddddddddd"
      start (System/currentTimeMillis)]
  
  ;; Add 3 votes synchronously
  (<!! (log/add-vote! log proposal-id #uuid "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa" "sig-a"))
  (println "Vote 1 added:" (- (System/currentTimeMillis) start) "ms")
  
  (<!! (log/add-vote! log proposal-id #uuid "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb" "sig-b"))
  (println "Vote 2 added:" (- (System/currentTimeMillis) start) "ms")
  
  (<!! (log/add-vote! log proposal-id #uuid "cccccccc-cccc-cccc-cccc-cccccccccccc" "sig-c"))
  (println "Vote 3 added:" (- (System/currentTimeMillis) start) "ms")
  
  ;; Check quorum
  (let [has-q (<!! (log/has-quorum? log proposal-id validator-set))]
    (println "Has quorum?" has-q "at" (- (System/currentTimeMillis) start) "ms")))

(println "\nTesting concurrent vote processing...")

(let [store (<!! (new-mem-store))
      validator-set {#uuid "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa" "pubkey-a"
                     #uuid "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb" "pubkey-b"
                     #uuid "cccccccc-cccc-cccc-cccc-cccccccccccc" "pubkey-c"}
      log (log/create-consensus-log store validator-set)
      proposal-id #uuid "eeeeeeee-eeee-eeee-eeee-eeeeeeeeeeee"
      start (System/currentTimeMillis)]
  
  ;; Add 3 votes concurrently (like handlers do)
  (go-loop []
    (<! (log/add-vote! log proposal-id #uuid "aaaaaaaa-aaaa-aaaa-aaaa-aaaaaaaaaaaa" "sig-a"))
    (println "Concurrent vote 1 added:" (- (System/currentTimeMillis) start) "ms"))
    
  (go-loop []
    (<! (log/add-vote! log proposal-id #uuid "bbbbbbbb-bbbb-bbbb-bbbb-bbbbbbbbbbbb" "sig-b"))
    (println "Concurrent vote 2 added:" (- (System/currentTimeMillis) start) "ms"))
    
  (go-loop []
    (<! (log/add-vote! log proposal-id #uuid "cccccccc-cccc-cccc-cccc-cccccccccccc" "sig-c"))
    (println "Concurrent vote 3 added:" (- (System/currentTimeMillis) start) "ms"))
  
  ;; Wait and check quorum
  (<!! (clojure.core.async/timeout 100))
  (let [has-q (<!! (log/has-quorum? log proposal-id validator-set))]
    (println "Has quorum after 100ms?" has-q)))

(System/exit 0)
