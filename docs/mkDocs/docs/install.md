# How to Install

This sections documents how to install LH and its dependencies.

## External Software Requirements

In order to use LiquidHaskell, you will need a [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
installed on your system. Download and install at least one of:

* [Z3](https://github.com/Z3Prover/z3) or [Microsoft official binary](https://github.com/Z3Prover/z3/releases)
* [CVC4](https://cvc4.github.io/)
* [MathSat](https://mathsat.fbk.eu/)

When in doubt, install Z3, which is the SMT solver most tested with LiquidHaskell.

Note: The SMT solver binary should be on your `PATH`; LiquidHaskell will execute it as a child process.

## Installing LiquidHaskell

LiquidHaskell itself is installed&enabled by adding it as a dependency in your project's `.cabal` file.

Depending on your version of GHC, you might want to use a build of LiquidHaskell from github or from Hackage.

* `ghc-9.10.1`: use liquidhaskell-0.9.10.1 from Hackage or use LiquidHaskell from github
* `ghc-9.8.2`: use liquidhaskell-0.9.8.2 from Hackage
* `ghc-9.6.3`: use liquidhaskell-0.9.6.3 from Hackage
* `ghc-9.4.7`: use liquidhaskell-0.9.4.7.0 from Hackage

Newer versions of GHC aren't supported yet.

To use liquidhaskell from Hackage, add `liquidhaskell` to the `build-depends`
section of your `.cabal` file, as you would any other dependency.

This causes `cabal` to automatically:

1. Install LiquidHaskell
2. Tell GHC to use LH during compilation in modules that contain the pragma `{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}`
3. Display liquid type errors during compilation
4. Integrate LH with `ghci`, `ghcid` and all GHC compatible tooling for your favorite editor.

`stack` requires some further configuration to indicate which version of `liquidhaskell`
and dependencies to use. See [this repository](https://github.com/ucsd-progsys/lh-plugin-demo)
for example `stack.yaml` files.

## Examples

The following concrete examples show the LiquidHaskell plugin in action:

- [Example Project 1](https://github.com/ucsd-progsys/lh-plugin-demo)
- [Example Project 2](https://github.com/ucsd-progsys/lh-plugin-demo-client) (uses Example Project 1 as a dependency)

You can use the `.cabal`, `stack.yaml` and `cabal.project` files in the
example packages to see how to write the equivalent files for your own
codebase.

### Liquid Dependencies

If you project depends on some well known library package `foo` (e.g. `base` or `vector`), then it's likely that the LiquidHaskell developers have written some specs for it. For boot libraries, that is those comming with the compiler, they are provided without further configuration. For other libraries like `vector`, a package like `liquid-vector` needs to be added to your `build-depends`.

In order to see what specs are used for boot libraries, you can check the
modules in [src](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/src).

For the vector library, you can find the specs [here](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/liquid-vector).

In general, whenever your module imports another module `A.B.C`, Liquid Haskell
will look for additional specs in any module of packages in `build-depends` with name
`A.B.C_LHAssumptions`.

### Editor Integration

Since LiquidHaskell is implemented as a GHC plugin, you get to automatically reuse **all** `ghc`-based support
for your editor as is. The sample packages include examples for `vscode`, `vim` and `emacs`.

### Uninstallation

Just remove the `liquid` packages from your `build-depends` again, and GHC won't use LiquidHaskell anymore.
You may also want to delete the `.liquid` directories placed alongside your source files (they contain debug information).

## Other Options

**Online Demo**: For small projects without a `.cabal` file, you can paste your code into the [online demo](http://goto.ucsd.edu:8090/index.html).
