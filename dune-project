(lang dune 2.0)

(name microc-lang)

(generate_opam_files true)

(authors "Yuri Andriaccio, LCI-2022")

(maintainers "Yuri Andriaccio, LCI-2022")

(license ISC)

(using menhir 2.0)

(package
 (name microc-lang)
 (synopsis "microc is a simple subset of the C language.")
 (description "microc is a simple subset of the C language.")
 (depends 
  (ocaml (>= 4.14)) 
   dune
   menhir
   ppx_deriving
   (llvm (>= 12.0.0))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
