(ns urd.consensus.substrate-portability-test
  "The half of the substrate the ClojureScript job did not compile.

  urd claims to be a portable clj+cljs consensus library. That was true of the
  algorithms, `sim.cljc`, `node.cljc` and `pending.cljc` -- and FALSE of
  `runtime.cljc` and `network.cljc`, which did not compile under ClojureScript
  at all. Nothing noticed, because the runner loaded the half that worked.

  Two causes, both now fixed:

  - `network.cljc` called `System/currentTimeMillis` with no reader conditional.
  - `runtime.cljc` referred `go` only in its `:clj` branch, and -- the harder
    one -- used `superv.async/go-loop-try-`, whose 0.3.50 definition unquotes
    the supervisor VALUE into the expansion (`(go-try- ~S ...)`). `S` holds
    channels, so the macro emits a literal channel: an object reference on the
    JVM, and an uncompilable constant under ClojureScript.

  These tests are deliberately thin. Their job is to make the compiler LOAD
  these namespaces on a JavaScript runtime, because that is the check that was
  missing. A portable file no ClojureScript job compiles is not portable, it is
  untested -- the same trap the seeded PRNG and the pending pool each fell into
  before it."
  (:require [clojure.test :refer [deftest testing is]]
            [urd.consensus.runtime :as rt]
            [urd.consensus.network :as net]
            [urd.consensus.store :as store]
            [urd.consensus.auth :as auth]
            [urd.consensus.trace :as trace]
            [urd.consensus.node :as n]))

(deftest the-runtime-namespace-loads-on-both-platforms
  (testing "loading it at all is the point; these are the smallest honest
            assertions that require it to have loaded"
    (is (= 100 rt/default-tick-ms))
    (is (= :direct rt/direct-topic))
    (is (fn? rt/start-runtime!))
    (is (fn? rt/send-event!))
    (is (fn? rt/last-error))
    (is (fn? rt/dropped-messages))))

(deftest the-network-namespace-loads-on-both-platforms
  (testing "`MockNetwork/broadcast!` stamped a timestamp with a bare
            `System/currentTimeMillis`, which does not exist in ClojureScript"
    (is (some? (net/create-mock-network :p1)))))

(deftest the-store-and-auth-namespaces-load-on-both-platforms
  (testing "`auth` is the verification edge and exists BECAUSE cljs Web Crypto
            is promise-based; a version of it that cljs cannot compile would be
            a joke at its own expense"
    (is (some? (store/memory-store)))
    (is (some? (auth/authenticator :none :p1)))
    ;; NOT asserting on `unseal`'s result: it returns a CHANNEL on both
    ;; platforms, which is the entire reason this namespace exists -- cljs Web
    ;; Crypto is promise-based, so verification cannot be synchronous. Reading
    ;; it here would need a go block, and the value is covered by `auth_test`
    ;; on the JVM anyway. What this file is for is making the compiler load it.
    (is (satisfies? auth/MessageAuth (auth/authenticator :none :p1)))))

(deftest the-trace-namespace-loads-on-both-platforms
  (is (some? (trace/tracing (reify n/Node
                              (capabilities [_] {:emits #{} :topics #{}})
                              (init [_ _] {:state {} :effects []})
                              (step [_ s _] {:state s :effects []}))))))
