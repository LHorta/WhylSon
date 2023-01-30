(lang dune 2.7)

(name whylson)

(generate_opam_files true)

(source
 (uri "git+https://gitlab.com/releaselab/fresco/michelson.git"))

(bug_reports "https://gitlab.com/releaselab/fresco/michelson/issues")

(homepage "https://gitlab.com/releaselab/fresco/michelson")

(license MIT)

(authors
 "Jo\195\163o Santos Reis <joao.reis@ubi.pt>"
 "Lu\195\173s Pedro Arrojado da Horta <luis.horta@ubi.pt>"
 "M\195\161rio Pereira <mariojppereira@gmail.com>")

(maintainers
 "Jo\195\163o Santos Reis <joao.reis@ubi.pt>"
 "Lu\195\173s Pedro Arrojado da Horta <luis.horta@ubi.pt>"
 "M\195\161rio Pereira <mariojppereira@gmail.com>")

(package
 (name whylson)
 (synopsis "A Why3 plugin to read Michelson files")
 (depends
  (dune :build)
  zarith
  why3
  michelson))
