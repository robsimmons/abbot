(lang dune 2.7)
(name abbot)
(version 0.2)
(using menhir 1.0)
(generate_opam_files true)

(authors "Bill Duff <wduff11@gmail.com>" "Rob Simmons")
(license "Apache-2.0")
(maintainers "Bill Duff <wduff11@gmail.com>")
(homepage "https://github.com/robsimmons/abbot")
(bug_reports "https://github.com/robsimmons/abbot/issues")

(package
 (name abbot)
 (synopsis "An SML and OCaml code generator for Abstract Binding Trees")
 (depends
  (core (>= v0.14.1))
  (core_unix (>= v0.16.0))
  (menhir (>= 20201201))
  (ocamlgraph (>= 2.0.0))
  (ppx_jane (>= v0.14.0))
  (ppxlib (>= 0.22.2))))

(package
 (name abbot_runtime)
 (synopsis "The runtime OCaml library needed by Abbot generated code (see package abbot)")
 (depends
  (core (>= v0.14.1))))
