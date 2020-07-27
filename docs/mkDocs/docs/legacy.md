# Installing and Running the Legacy LiquidHaskell Executable

**We strongly recommend** that you use the [GHC Plugin](plugin.md) 
available in version 0.8.10 onwards, as the legacy executable is deprecated and has been 
kept around for backwards compatibility. It will eventually be removed from future LH releases.

## External software requirements

Make sure all the required [external software](external.md) software is installed before proceeding.

## Installation options

You can install the `liquid` binary via package manager *or* source.

### Via Package Manager

Simply do:

    cabal install liquidhaskell

We are working to put `liquid` on `stackage`.

You can designate a specific version of LiquidHaskell to
ensure that the correct GHC version is in the environment. 
For example:

    cabal install liquidhaskell-0.8.10.1

### Build from Source

If you want the most recent version, you can build from source as follows,
either using `stack` (recommended) or `cabal`. In either case:

1. *recursively* `clone` the repo:

    ```git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git```

2. Go inside the `liquidhaskell` directory:

    ```
    cd liquidhaskell
    ```

3. Build the package:

    a. with [stack][stack]:

        stack install liquidhaskell

    b. or with [cabal][cabal]:

        cabal v2-build liquidhaskell

## Running in GHCi

To run inside `ghci` e.g. when developing do:

```bash
$ stack ghci liquidhaskell
ghci> :m +Language.Haskell.Liquid.Liquid
ghci> liquid ["tests/pos/Abs.hs"]
```

[stack]: https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md
[cabal]: https://www.haskell.org/cabal/
