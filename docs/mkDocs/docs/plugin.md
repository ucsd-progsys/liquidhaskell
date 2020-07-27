# Installing and Running LiquidHaskell

As of LH version 0.8.10, mirroring GHC-8.10, LiquidHaskell 
is available as a [GHC compiler plugin](https://downloads.haskell.org/~ghc/8.10.1/docs/html/users_guide/extending_ghc.html). 

(We still offer the old [legacy executable](legacy.md), to give users enough time to complete migrations
to the new system.)

## Benefits

As a GHC plugin, you simply specify `liquidhaskell` as one of the dependencies 
of your project in the cabal file, after which `stack` or `cabal` automatically:

1. Install Liquidhaskell 
2. Tells GHC to use LH during compilation
3. Displays refinement type errors during compilation
4. Reuses `ghci`, `ghcid` and all GHC compatible tooling for your favorite editor. 

**We recommend switching to the new compiler plugin as soon as possible.**

## External software requirements

Make sure all the required [external software](install.md) software is installed before proceeding.

## Getting started

We offer a detailed "getting started" walkthrough in the form of a documented Haskell module. 
You can read it [here](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/src/Language/Haskell/Liquid/GHC/Plugin/Tutorial.hs).

## Examples

The following concrete examples show the source plugin in action:

- [Sample package](https://github.com/ucsd-progsys/lh-plugin-demo)
- [Sample client package](https://github.com/ucsd-progsys/lh-plugin-demo-client)

You can use the `.cabal`, `stack.yaml` and `cabal.project` files in the 
sample packages to see how to write the equivalent files for your own 
codebase.

## Editor Support

One of the added benefit of the plugin is that you get to automatically reuse **all** ghc-based support
for your editor as is. Again, the sample packages include examples for `vscode`, `vim` and `emacs`.
