(lang dune 1.11)
(name why3michelson)
(using menhir 1.0)

(generate_opam_files true)

(source (uri "git+https://gitlab.com/releaselab/fresco/michelson.git"))
(bug_reports "https://gitlab.com/releaselab/fresco/michelson/issues")
(homepage "https://gitlab.com/releaselab/fresco/michelson")
(license MIT)
(authors "João Santos Reis <joao.reis@ubi.pt>" "Luís Pedro Arrojado da Horta <luis.horta@ubi.pt>" "Mário Pereira <mariojppereira@gmail.com>")
(maintainers "João Santos Reis <joao.reis@ubi.pt>" "Luís Pedro Arrojado da Horta <luis.horta@ubi.pt>" "Mário Pereira <mariojppereira@gmail.com>")

(package
 (name why3michelson)
 (synopsis "A Why3 plugin to read Michelson files")
 (depends
  (dune :build)
  (zarith :dev)))
