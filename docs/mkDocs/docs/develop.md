# Developers' Guide

Here are some notes that are generally useful for people *developing* LH itself.

## Fast (re)compilation

When working on the `liquidhaskell` library, usually all we want is to make changes and quickly recompile
only the bare minimum, to try out new ideas. Using a fully-fledged GHC plugin doesn't help in this sense,
because packages like `liquid-base` or `liquid-ghc-prim` all have a direct dependency on `liquidhaskell`, and
therefore every time the latter changes, an expensive rebuild of those packages is triggered, which
might become tedious overtime. To mitigate this, we offer a faster, "dev-style" build mode which is based
on the assumption that most changes to the `liquidhaskell` library do not alter the validity of
already-checked libraries, and therefore things like `liquid-base` and `liquid-ghc-prim` can be considered
"static assets", avoiding the need for a recompilation. In other terms, we explicitly disable recompilation
of any of the `liquid-*` ancillary library in dev mode, so that rebuilds would also influence the 
`liquidhaskell` library.

### Usage and recommended workflow

This is how you can use this:

* To begin with, perform a **full** build of **all** the libraries, by doing either `cabal v2-build` or `stack build`,
  **without** specifying any extra environment variables from the command line. This is needed to ensure that
  we things like `liquid-base` and `liquid-ghc-prim` are compiled at least once, as we would need the
  refinements they contain to correctly checks other downstream programs;

* At this point, the content of the `liquid-*` packages is considered "trusted" and "frozen", until you won't
  force another full, _non-dev_ build;

* In order to quickly test changes to the `liquidhaskell` library without recompiling the `liquid-*` packages,
  we need to start a build passing the `LIQUID_DEV_MODE` env var as part of the build command. Examples:

#### Stack

```
env LIQUID_DEV_MODE=true stack build
```

#### Cabal

```
LIQUID_DEV_MODE=true cabal v2-build
```

It's also possible (but not recommended) to add `LIQUID_DEV_MODE` to .bashrc or similar, but this would
permanently disable building the `liquid-*` packages, and this might silently mask breaking changes to the
`liquidhaskell` library that would manifest only when compiling these other packages.

If you wish to force building all the libraries again, it's sufficient to issue the same builds commands 
without the `LIQUID_DEV_MODE`.

## How To Run Regression Tests

You can run all the tests by

    $ stack test

To pass in specific parameters and run a subset of the tests 

    $ stack test liquidhaskell --fast  --test-arguments "--liquid-opts --no-termination -p Unit"

Or your favorite number of threads, depending on cores etc.

You can directly extend and run the tests by modifying

    tests/test.hs

## How to Profile

1. Build with profiling on

    ```
    $ stack build liquidhaskell --fast --profile
    ```


2. Run with profiling

    ```
    $ stack exec -- liquid range.hs +RTS -hc -p
    $ stack exec -- liquid range.hs +RTS -hy -p
    ```

    Followed by this which shows the stats file

    ```
    $ more liquid.prof
    ```

    or by this to see the graph

    ```
    $ hp2ps -e8in -c liquid.hp
    $ gv liquid.ps
    ```

    etc.

## How to Get Stack Traces On Exceptions

1. Build with profiling on

    ```
    $ stack build liquidhaskell --fast --profile
    ```

2. Run with backtraces

    ```
    $ liquid +RTS -xc -RTS foo.hs
    ```

    ```
    stack exec -- liquid List00.hs +RTS -p -xc -RTS
    ```

## Working With Submodules

To update the `liquid-fixpoint` submodule, run:

```
cd ./liquid-fixpoint
git fetch --all
git checkout <remote>/<branch>
cd ..
```

This will update `liquid-fixpoint` to the latest version on `<branch>` (usually `master`) 
from `<remote>` (usually `origin`). After updating `liquid-fixpoint`, make sure to include this change in a
commit! Running:

```
git add ./liquid-fixpoint
```

will save the current commit hash of `liquid-fixpoint` in your next commit to the `liquidhaskell` repository.
For the best experience, **don't** make changes directly to the `./liquid-fixpoint` submodule, or else git
may get confused. Do any `liquid-fixpoint` development inside a separate clone/copy elsewhere. If something
goes wrong, run:

```
rm -r ./liquid-fixpoint
git submodule update --init
```

to blow away your copy of the `liquid-fixpoint` submodule and revert to the last saved commit hash.

Want to work fully offline? `git` lets you add a local directory as a remote. Run:

```
cd ./liquid-fixpoint
git remote add local /path/to/your/fixpoint/clone
cd ..
```

Then to update the submodule from your local clone, you can run:

```
cd ./liquid-fixpoint
git fetch local
git checkout local/<branch>
cd ..
```

## Releasing on Hackage

*NOTE: The following section is relevant only for few developers, i.e. the ones which are directly involved
in the release process. Most contributors can skip this section.*

We provide a conveniency script to upload all the `liquid-*` packages (**including** `liquid-fixpoint`) on
Hackage, in a lockstep fashion. To do so, it's possible to simply run the `scripts/release_to_hackage.sh`
Bash script. The script doesn't accept any argument and it tries to determine the packages
to upload by scanning the `$PWD` for packages named appropriately. It will ask the user for confirmation
before proceeding, and `stack upload` will be used under the hood.

