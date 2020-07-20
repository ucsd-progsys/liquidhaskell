# Installing and Running the Legacy LiquidHaskell Executable

**We strongly recommend** that you use the [GHC Plugin](plugin.md) 
available in version 0.8.10 onwards. The legacy executable has been 
kept around for backwards compatibility but will eventually be deprecated.


## Install

To run the legacy LiquidHaskell executable you need to install:

1. An SMT solver
2. LH itself as a standalone binary

You can install the `liquid` binary via package manager *or* source.

### 1. Install SMT Solver

Download and install *at least one* of

+ [Z3](https://github.com/Z3Prover/z3/releases) or [Microsoft official binary](https://www.microsoft.com/en-us/download/details.aspx?id=52270)
+ [CVC4](http://cvc4.cs.stanford.edu/web/)
+ [MathSat](http://mathsat.fbk.eu/download.html)

**Note:** The SMT solver binary should be on your `PATH`; LiquidHaskell will execute it as a child process.

### 2. Install Legacy Binary

You can install the `liquid` binary via package manager *or* source.

#### Via Package Manager

The `liquid` executable is provided as part of a standalone,
battery-included package called `liquid-platform`.

Simply do:

    cabal install liquid-platform

We are working to put `liquid` on `stackage`.

You can designate a specific version of LiquidHaskell to
ensure that the correct GHC version is in the environment. 
As an example,

    cabal install liquid-platform-0.9.0.0

#### Build from Source

If you want the most recent version, you can build from source as follows,
either using `stack` (recommended) or `cabal`. In either case:

1. *recursively* `clone` the repo 

    git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
    cd liquidhaskell

2. `build` the package with [stack][stack] 

    stack install liquid-platform

3. or with [cabal][cabal] 

    cabal v2-build liquid-platform

#### A note on the GHC_PACKAGE_PATH

To work correctly `liquid` requires access to auxiliary packages
installed as part of the executable. Therefore, you might need to 
extend your `$GHC_PACKAGE_PATH` to have it point to the right location(s). 

Typically the easiest way is to call `stack path`, which will print 
a lot of diagnostic output. From that it should be suffient to copy 
the paths printed as part of `ghc-package-path: <some-paths>` and 
extend the `GHC_PACKAGE_PATH` this way (typically editing your `.bashrc` 
to make the changes permanent):

```
export GHC_PACKAGE_PATH=$GHC_PACKAGE_PATH:<some-paths>
```

After that, running `liquid` anywhere from the filesystem should work.

### Troubleshooting

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

## Running the Legacy Binary

To verify a file called `foo.hs` at type

```bash
$ liquid foo.hs
```

## Running in GHCi

To run inside `ghci` e.g. when developing do:

```bash
$ stack ghci liquidhaskell
ghci> :m +Language.Haskell.Liquid.Liquid
ghci> liquid ["tests/pos/Abs.hs"]
```


[stack]: https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md
[cabal]: https://www.haskell.org/cabal/