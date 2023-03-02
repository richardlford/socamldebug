(lang dune 3.8)

(name socamldebug)

(generate_opam_files true)
(map_workspace_root true)

(source
 (github richardlford/socamldebug))

(authors "Richard L Ford")

(maintainers "Richard L Ford")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name socamldebug)
 (synopsis "Standalone OCaml Debugger")
 (description "An adaptation of the standard ocamldebug that can be built separately")
 (depends ocaml dune sdebugger)
 (tags
  (topics ocaml debugger)))

(package
 (name sdebugger)
 (synopsis "Standalone OCaml Debugger Library")
 (description "Library for an adaptation of the standard ocamldebug that can be built separately")
 (depends ocaml dune soc_compat)
 (tags
  (topics ocaml debugger)))

(package
 (name soc_compat)
 (synopsis "Standalone OCaml Compatibility Library")
 (description "Standalone OCaml utility compatibility Library")
 (depends ocaml dune compiler-libs str unix)
 (tags
  (topics ocaml)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
