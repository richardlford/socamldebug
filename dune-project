(lang dune 3.8)

(name socamldebug)

(generate_opam_files true)

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
 (depends ocaml dune)
 (tags
  (topics ocaml debugger)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
