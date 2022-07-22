# Install LiquidHaskell

To run `liquid` you need to install:

1. An SMT solver
2. The `liquid` binary via package manager *or* source.


## Step 1: Install SMT Solver

Download and install *at least one* of

+ [Z3](https://github.com/Z3Prover/z3/releases) or [Microsoft official binary](https://www.microsoft.com/en-us/download/details.aspx?id=52270)
+ [CVC4](http://cvc4.cs.stanford.edu/web/)
+ [MathSat](http://mathsat.fbk.eu/download.html)

Note: It should be findable from PATH. LiquidHaskell is executing it as a child process.

## Step 2: Install `liquid` via Package Manager

The `liquid` executable is provided as part of a standalone, battery-included package called `liquid-platform`.

Simply do:

    cabal install liquid-platform

We are working to put `liquid` on `stackage`.

You can designate a specific version of LiquidHaskell to ensure that the correct
GHC version is in the environment. As an example,

    cabal install liquid-platform-0.9.0.0

## Step 2: Install `liquid` from Source

If you want the most recent version, you can build from source as follows,
either using `stack` (recommended) or `cabal`. In either case: *recursively*
clone the repo and then build:

### Build with `stack` (recommended)

This requires that you have installed [stack][stack] (which we strongly recommend!)

    git clone --recursive git@github.com:ucsd-progsys/liquidhaskell.git
    cd liquidhaskell
    stack install liquid-platform

If you haven't set up your ssh keys with github, use the `https` method to clone and build

    git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
    cd liquidhaskell
    stack install liquid-platform

#### A note on the GHC_PACKAGE_PATH

In order for `liquid` to work correctly, it needs to have access to auxiliary packages
installed as part of the executable. Therefore, you might need to extend your `$GHC_PACKAGE_PATH` to
have it point to the right location(s). Typically the easiest way is to call `stack path`, which will
print a lot of diagnostic output. From that it should be suffient to copy the paths printed as part of
`ghc-package-path: <some-paths>` and extend the `GHC_PACKAGE_PATH` this way 
(typically editing your `.bashrc` to make the changes permanent):

```
export GHC_PACKAGE_PATH=$GHC_PACKAGE_PATH:<some-paths>
```

After that, running `liquid` anywhere from the filesystem should work.


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
