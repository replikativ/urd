(ns urd.cljs-test-runner
  "Runs the portable test namespaces under a JavaScript runtime.

  Only `.cljc` namespaces belong here. The point is not coverage -- the JVM
  suite is far larger -- but to make the PORTABILITY claim falsifiable. Values
  that must be identical on both platforms are asserted on both platforms,
  rather than asserted on one and hoped for on the other.

  Exits non-zero on failure so CI actually fails."
  (:require [clojure.test :as t]
            [urd.consensus.algorithms.scp-portability-test]
            [urd.consensus.portability-test]
            [urd.consensus.sim-portability-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println "\n" (:test m) "tests," (:pass m) "assertions,"
           (:fail m) "failures," (:error m) "errors")
  (when-not (t/successful? m)
    (js/process.exit 1)))

(defn -main [& _]
  (t/run-tests 'urd.consensus.algorithms.scp-portability-test
               'urd.consensus.portability-test
               'urd.consensus.sim-portability-test))

(set! *main-cli-fn* -main)
