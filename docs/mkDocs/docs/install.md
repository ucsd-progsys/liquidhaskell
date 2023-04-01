# How to Install

This sections documents how to install LH and its dependencies.

## External Software Requirements

In order to use LiquidHaskell, you will need a [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
installed on your system. Download and install at least one of:

* [Z3](https://github.com/Z3Prover/z3) or [Microsoft official binary](https://github.com/Z3Prover/z3/releases)
* [CVC4](https://cvc4.github.io/)
* [MathSat](https://mathsat.fbk.eu/)

Note: The SMT solver binary should be on your `PATH`; LiquidHaskell will execute it as a child process.

## Installing LiquidHaskell

LiquidHaskell itself is installed&enabled by adding it as a dependency in your project's `.cabal` file.

Just add `liquidhaskell` to the `build-depends` section of your `.cabal` file, as you would any other dependency.

This causes `stack` (or `cabal`) to automatically:

1. Install LiquidHaskell
2. Tell GHC to use LH during compilation
3. Display liquid type errors during compilation
4. Integrate LH with `ghci`, `ghcid` and all GHC compatible tooling for your favorite editor.

## Examples

The following concrete examples show the LiquidHaskell plugin in action:

- [Example Project 1](https://github.com/ucsd-progsys/lh-plugin-demo)
- [Example Project 2](https://github.com/ucsd-progsys/lh-plugin-demo-client) (uses Example Project 1 as a dependency)

You can use the `.cabal`, `stack.yaml` and `cabal.project` files in the
sample packages to see how to write the equivalent files for your own
codebase.

### Liquid Dependencies

If you project depends on some well known library package `foo` (e.g. `base` or `containers`), then it's likely that the LiquidHaksell developers have annotated it with Liquid Types. You can use these annotations by adding the `liquid-foo` package to your `build-depends`.

### Editor Integration

Since LiquidHaskell is implemented as a GHC plugin, you get to automatically reuse **all** `ghc`-based support
for your editor as is. The sample packages include examples for `vscode`, `vim` and `emacs`.

### Uninstallation

Just remove the `liquid` packages from your `build-depends` again, and GHC won't use LiquidHaskell anymore.
You may also want to delete the `.liquid` directories placed alongside your source files (they contain debug information).

## Other Options

**Online Demo**: For small projects without a `.cabal` file, you can paste your code into the [online demo](http://goto.ucsd.edu:8090/index.html).
