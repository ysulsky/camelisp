(lang dune 3.18)

(name scaml)

(generate_opam_files true)

(source
 (github ysulsky/scaml))

(authors "Yury Sulsky <yury.sulsky@gmail.com>")

(license LICENSE)

(package
 (name scaml)
 (synopsis "Elisp to OCaml Transpiler")
 (description "Efficiently execute elisp by transpiling to OCaml")
 (depends
  (ocaml
   (>= 4.14.0))
  (dune
   (>= 3.11))
  base
  (core
   (>= v0.15.0))
  (core_unix
   (>= v0.15.0))
  (sexplib
   (>= v0.15.0))
  (ppx_sexp_conv
   (>= v0.15.0))
  (ppx_inline_test
   (>= v0.15.0))
  (ppx_compare (>= v0.15.0))
  (ppx_let (>= v0.15.0))
  fmt
  (alcotest
   (>= 1.7.0))
  dynlink
  unix)
 (tags
  (elisp interpreter transpiler)))
