(ns build
  "Build and publish urd.

  Mirrors the rest of the replikativ stack (kabel, geheimnis, boring) so that
  the release story is the same everywhere: version is `major.minor.<commit
  count>`, the jar carries a pom with real SCM data, and `deploy` goes to
  Clojars.

  This namespace did not exist while `deps.edn` already declared
  `:build {:ns-default build}` and CircleCI already chained
  `build -> deploy -> release`. That chain therefore could never have run, and
  urd has never been publishable -- which is worth stating rather than quietly
  fixing, because the badge and the install snippet in the README both implied
  otherwise."
  (:require [clojure.tools.build.api :as b]
            [deps-deploy.deps-deploy :as dd]))

(def lib 'org.replikativ/urd)
(def major 0)
(def minor 1)

(defn commit-count [] (b/git-count-revs nil))
(defn version [] (format "%d.%d.%s" major minor (commit-count)))

(def class-dir "target/classes")
(defn jar-file [] (format "target/%s-%s.jar" (name lib) (version)))
(def basis (delay (b/create-basis {:project "deps.edn"})))

(defn clean [_]
  (b/delete {:path "target"}))

(defn jar [_]
  (let [v (version)
        jf (jar-file)]
    (b/write-pom {:class-dir class-dir
                  :lib lib
                  :version v
                  :basis @basis
                  :src-dirs ["src"]
                  :scm {:url "https://github.com/replikativ/urd"
                        :connection "scm:git:git://github.com/replikativ/urd.git"
                        :developerConnection "scm:git:ssh://git@github.com/replikativ/urd.git"
                        :tag (b/git-process {:git-args "rev-parse HEAD"})}
                  :pom-data [[:description
                              "Portable consensus algorithms for Clojure and ClojureScript."]
                             [:url "https://github.com/replikativ/urd"]
                             [:licenses
                              [:license
                               ;; 2.0, matching `LICENSE`. The stack's older
                               ;; build files say 1.0 and copying one would have
                               ;; published a pom that contradicts the file in
                               ;; the repository.
                               [:name "Eclipse Public License 2.0"]
                               [:url "https://www.eclipse.org/legal/epl-2.0/"]]]]})
    (b/copy-dir {:src-dirs ["src"] :target-dir class-dir})
    (b/jar {:class-dir class-dir :jar-file jf})
    (println "JAR created:" jf)))

(defn deploy [_]
  (jar nil)
  (dd/deploy {:installer :remote
              :artifact (jar-file)
              :pom-file (b/pom-path {:lib lib :class-dir class-dir})})
  (println "Deployed to Clojars!"))

(defn install [_]
  (jar nil)
  (b/install {:basis @basis
              :lib lib
              :version (version)
              :jar-file (jar-file)
              :class-dir class-dir})
  (println "Installed to local Maven repo"))
