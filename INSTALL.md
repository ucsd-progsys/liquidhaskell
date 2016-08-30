# Install LiquidHaskell

To run `liquid` you need to install:

1. An SMT solver
2. The `liquid` binary via package manager *or* source.


## Step 1: Install SMT Solver

Download and install *at least one* of

+ [Z3](https://github.com/Z3Prover/z3/releases)
+ [CVC4](http://cvc4.cs.nyu.edu/)
+ [MathSat](http://mathsat.fbk.eu/download.html)


## Step 2: Install `liquid` via Package Manager

Simply do:

    cabal install liquidhaskell

We are working to put `liquid` on `stackage`.

## Step 2: Install `liquid` from Source

If you want the most recent version, you can build from source as follows,
either using `stack` (recommended) or `cabal`. In either case: *recursively*
clone the repo and then build:

### Build with `stack` (recommended)

This requires that you have installed [stack][stack] (which we strongly recommend!)

    git clone --recursive git@github.com:ucsd-progsys/liquidhaskell.git
    cd liquidhaskell
    stack install

## Build with `cabal`

    git clone --recursive git@github.com:ucsd-progsys/liquidhaskell.git
    cd liquidhaskell

    cabal sandbox init
    cabal sandbox add-source ./liquid-fixpoint
    cabal sandbox add-source ./prover
    cabal install

## Troubleshooting


1. If you're on Windows, please make sure the SMT solver is installed
    in the **same** directory as LiquidHaskell itself (i.e. wherever
    `cabal` or `stack` puts your binaries). That is, do:

    ```
    which liquid
    ```

    and make sure that `z3` or `cvc4` or `mathsat` are in the `PATH`
    returned by the above.

2. If you installed via `stack` and are experiencing path related woes, try:

    ```
    stack exec -- liquid path/to/file.hs
    ```

[stack]: https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md
