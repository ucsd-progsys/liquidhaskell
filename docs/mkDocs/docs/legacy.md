# Installing the Legacy LiquidHaskell Executable

**We strongly recommend** that you use the [GHC Plugin](plugin.md) 
available in version 0.8.10 onwards, as the legacy executable is deprecated and has been 
kept around for backwards compatibility. It will eventually be removed from future LH releases.

## External software requirements

Make sure all the required [external software](install.md) software is installed before proceeding.

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

## Incremental Checking

The LiquidHaskell executable supports *incremental* checking where each run only checks
the part of the program that has been modified since the previous run.

```
    $ liquid --diff foo.hs
```

Each run of `liquid` saves the file to a `.bak` file and the *subsequent* run does a `diff` to see what
has changed w.r.t. the `.bak` file only generates constraints for the `[CoreBind]` corresponding to the
changed top-level binders and their transitive dependencies.

The time savings are quite significant. For example:

```
    $ time liquid --notermination -i . Data/ByteString.hs > log 2>&1

    real	7m3.179s
    user	4m18.628s
    sys	    0m21.549s
```

Now if you go and tweak the definition of `spanEnd` on line 1192 and re-run:

```
    $ time liquid -d --notermination -i . Data/ByteString.hs > log 2>&1

    real	0m11.584s
    user	0m6.008s
    sys	    0m0.696s
```

The diff is only performed against **code**, i.e. if you only change
specifications, qualifiers, measures, etc. `liquid -d` will not perform
any checks. In this case, you may specify individual definitions to verify:

```
    $ liquid -b bar -b baz foo.hs
```

This will verify `bar` and `baz`, as well as any functions they use.

If you always want to run a given file with diff-checking, add
the pragma:

    {-@ LIQUID "--diff" @-}




[stack]: https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md
[cabal]: https://www.haskell.org/cabal/
