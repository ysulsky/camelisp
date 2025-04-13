(lang dune 3.18)
(using menhir 2.0)
(name scaml)
(generate_opam_files true)
(source (github ysulsky/scaml))
(authors "Yury Sulsky <yury.sulsky@gmail.com>")
(license LICENSE)

(package
 (name scaml)
 (synopsis "Elisp to OCaml Transpiler")
 (description "Efficiently execute elisp by transpiling to OCaml")
 (depends
  (ocaml (>= 4.14.0))
  (dune (>= 3.11))
  base core core_unix
  sexplib ; Keep for Value.t sexp_of
  ppx_sexp_conv ; Keep for Value.t sexp_of
  ppx_inline_test ppx_compare ppx_let
  fmt alcotest dynlink unix menhir menhirLib ; Add menhir/menhirLib
  readline
  )
 (tags (elisp interpreter transpiler)))
