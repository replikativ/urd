(ns build
  "Build and publish Urd to Clojars."
  (:require [borkdude.gh-release-artifact :as gh]
            [clojure.tools.build.api :as b]
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
    (b/delete {:path class-dir})
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
                               [:name "Apache License, Version 2.0"]
                               [:url "https://www.apache.org/licenses/LICENSE-2.0"]]]]})
    (b/copy-dir {:src-dirs ["src"] :target-dir class-dir})
    (b/copy-file {:src "LICENSE" :target (str class-dir "/META-INF/LICENSE")})
    (b/copy-file {:src "NOTICE" :target (str class-dir "/META-INF/NOTICE")})
    (b/jar {:class-dir class-dir :jar-file jf})
    (println "JAR created:" jf)))

(defn deploy [_]
  (jar nil)
  (dd/deploy {:installer :remote
              :artifact (jar-file)
              :pom-file (b/pom-path {:lib lib :class-dir class-dir})})
  (println "Deployed to Clojars!"))

(defn release [_]
  (gh/overwrite-asset {:org "replikativ"
                       :repo (name lib)
                       :tag (version)
                       :commit (b/git-process {:git-args "rev-parse HEAD"})
                       :file (jar-file)
                       :content-type "application/java-archive"
                       :draft false}))

(defn install [_]
  (jar nil)
  (b/install {:basis @basis
              :lib lib
              :version (version)
              :jar-file (jar-file)
              :class-dir class-dir})
  (println "Installed to local Maven repo"))
