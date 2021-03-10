# WhylSon

WhylSon helps you prove your Michelson smart contract

## System Requirements

[OCaml](https://ocaml.org/docs/install.html) version 4.10.0

Use the [opam](https://opam.ocaml.org/doc/Install.html) package manager to install the following:

- [Dune](https://github.com/ocaml/dune) version 2.5.1

- [Why3](http://why3.lri.fr/) version 1.3.1

- [GtkSourceView2](https://wiki.gnome.org/Projects/GtkSourceView) version >= 2.0

## Installation

```bash
dune build @install 
dune install
why3 config --install-plugin $OPAM_SWITCH_PREFIX/lib/why3michelson/plugins/plugin_whylson.cmxs
```
For some reason if the `dune build @install` command fails, just run it again

## Usage

```bash
why3 ide -L [PATH_TO_WHYML/src] [yourFile.tz]
```
## Proof Examples

Some proof examples are located under `WhyML/tests` directory

For these examples just run
```bash
why3 ide -L [PATH_TO_WHYML/src] [example_file.mlw]
```

## Contributing
Pull requests are welcome. For major changes, please open an issue first to discuss what you would like to change.

Please make sure to update tests as appropriate.

## License
[MIT](https://choosealicense.com/licenses/mit/)
