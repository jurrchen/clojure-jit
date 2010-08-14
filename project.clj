(defproject clojure-jit "0.1"
  :description "Adds a just in time compiled gen-class"
  :dependencies [[org.clojure/clojure "1.2.0-RC1"]
                 [org.clojure/clojure-contrib "1.2.0-RC1"]]
  :aot [clojure.core.jit]
  :dev-dependencies [[org.clojars.mcav/lein-javac "1.0.1"]]
  )