# Catt_Strict

This repository implements an experimental typechecker for the languages Catt, Catt_su, and Catt_sua; type theories which model various semi-strictifications of higher categories (see [this thesis](https://arxiv.org/abs/2502.17068)). The typechecker here uses a bidirectional type checking algorithm to perform inference and utilises NbE to reduce terms to normal forms.

## Installation

The tool can be built with `cargo`, and should require no extra dependencies. A development environment is also provided through a nix flake with the correct versions of each tool, but it should not be necessary to use this.

To install locally run:

```bash
cargo install
```

alternatively, one can run `cargo run` from the build directory to directly compile and run the executable instead of installing it.

## Usage

To see all the available options run:

```bash
catt_strict --help
```

Files can be typechecked by adding them as command line arguments:

```bash
catt_strict examples/eh.catt examples/monoidal.catt
```

To turn on "sua" (or "su") normalisation, add the `--sua` (or `--su`) flag:

```bash
catt_strict --sua examples/syllepsis.catt
```

The `-i` flag starts an interactive command line REPL.

## LSP server

The tool comes with a very primitive LSP server, which supports reporting diagnostics for parsing and type errors. The server can be activated with the `--lsp` flag. Enabling this within your editor will be editor specific.






