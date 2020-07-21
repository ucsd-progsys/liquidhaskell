# Installing and Running LiquidHaskell

As of LH version 0.8.10, mirroring GHC-8.10, LiquidHaskell 
is available as a [GHC compiler plugin](https://downloads.haskell.org/~ghc/8.10.1/docs/html/users_guide/extending_ghc.html). 

(We still offer a [legacy executable](legacy.md) which uses 
the plugin internally, to give users enough time to complete 
migrations to the new system.)

## Benefits

As a GHC plugin, you simply specify `liquidhaskell` as one of the dependencies 
of your project in the cabal file, after which `stack` or `cabal` automatically:

1. Install Liquidhaskell 
2. Tells GHC to use LH during compilation
3. Displays refinement type errors during compilation
4. Reuses `ghci`, `ghcid` and all GHC compatible tooling for your favorite editor. 

**We recommend switching to the new compiler plugin as soon as possible.**

## Installation and Use

1. Install an SMT Solver Download and install at least one of

    Z3 or Microsoft official binary
    CVC4
    MathSat

Note: The SMT solver binary should be on your PATH; LiquidHaskell will execute it as a child process.

The following concrete examples show how the source plugin works

- [Tutorial documentation](src/Language/Haskell/Liquid/GHC/Plugin/Tutorial.hs) 
- [Sample package](https://github.com/ucsd-progsys/lh-plugin-demo)
- [Sample client package](https://github.com/ucsd-progsys/lh-plugin-demo-client)

You can use the `.cabal`, `stack.yaml` and `cabal.project` files in the 
sample packages to see how to write the equivalent files for your own 
codebase.

## Editor Support

**In plugin-mode** you get to automatically reuse **all** `ghc` 
based support for your editor as is. Again, the sample packages 
include examples for `vscode`, `vim` and `emacs`.

