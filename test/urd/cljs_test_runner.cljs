(ns urd.cljs-test-runner
  "Runs the portable test namespaces under a JavaScript runtime.

  Only `.cljc` namespaces belong here. The point is not coverage -- the JVM
  suite is far larger -- but to make the PORTABILITY claim falsifiable. Values
  that must be identical on both platforms are asserted on both platforms,
  rather than asserted on one and hoped for on the other.

  Exits non-zero on failure so CI actually fails."
  (:require [clojure.test :as t]
            [urd.consensus.pending-test]
            [urd.consensus.algorithms.scp-portability-test]
            [urd.consensus.portability-test]
            [urd.consensus.sim-portability-test]
            [urd.consensus.substrate-portability-test]
            [urd.konserve-checkpoint-test]
            [urd.auth-probe]
            [urd.wire-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println "\n" (:test m) "tests," (:pass m) "assertions,"
           (:fail m) "failures," (:error m) "errors")
  ;; Exit EXPLICITLY on success too. Node keeps running while anything holds
  ;; its event loop, and requiring the runtime brings core.async timers and a
  ;; mock network's channels with it -- so the suite passed and then hung, and
  ;; a hanging suite reports nothing at all, which is how a green run and a
  ;; broken one become indistinguishable.
  (js/process.exit (if (t/successful? m) 0 1)))

(defn -main [& _]
  (t/run-tests 'urd.consensus.algorithms.scp-portability-test
               'urd.consensus.portability-test
               'urd.consensus.sim-portability-test
               ;; The park-and-retry pool is shared by four algorithms and was
               ;; written as `.cljc` but never registered here, so it had no
               ;; ClojureScript coverage at all. A portable file that no
               ;; ClojureScript job compiles is not portable, it is untested --
               ;; which is the same trap the seeded PRNG fell into.
               'urd.consensus.pending-test
               ;; `runtime.cljc` and `network.cljc` did not compile under
               ;; ClojureScript AT ALL, and this runner is why nobody knew: it
               ;; loaded the algorithms and the simulator and never the
               ;; runtime. The job that exists to make the portability claim
               ;; falsifiable was not touching the half that was false.
               'urd.consensus.substrate-portability-test
               'urd.konserve-checkpoint-test
               'urd.auth-probe
               ;; The signing bytes, pinned to a literal produced by Python.
               ;; This is the ONE test whose value comes entirely from running
               ;; here as well as on the JVM: a clj-only run cannot tell a
               ;; cross-platform encoder from a per-platform one.
               'urd.wire-test))

(set! *main-cli-fn* -main)
