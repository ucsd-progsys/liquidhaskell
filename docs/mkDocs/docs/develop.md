# Developers' Guide

Here are some notes that are generally useful for people *developing* LH itself.

## Hacking on the GHC Plugin

For a more thorough walkthrough of the plugin architecture, [start here](develop/plugin_architecture.md).

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

_For a way of running the test suite for multiple GHC versions, consult the FAQs._

There are particular scripts for running LH in the different modes, e.g. for different 
compiler versions and in plugin mode or as standalone. These scripts are in:

    $ ./scripts/test

So you can run *all* the tests for say the ghc-8.10 version by

    $ ./scripts/test/test_810.sh

You can run a particular test instead by

    $ LIQUID_DEV_MODE=true ./scripts/test/test_810.sh BadDataDeclTyVars.hs

Note that the script uses the `BadDataDeclTyVars.hs` as a pattern so will run *all* tests that match.
So, for example,

    $ LIQUID_DEV_MODE=true ./scripts/test/test_810.sh Error-Messages

will run all the tests in the `Error-Messages` group.

To pass in specific parameters and run a subset of the tests  **FIXME**

    $ stack test liquidhaskell --fast  --test-arguments "--liquid-opts --no-termination -p Unit

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

## The GHC.API module

In order to allow LH to work with multiple GHC versions, we need a way to abstract over all the breaking
changes of the `ghc` library, which might change substantially with every major GHC release. This is
accomplished by the [GHC.API][] module. The idea is that **rather than importing multiple `ghc` modules,
LH developers must import this single module in order to write future-proof code**. This is especially
important for versions of the compiler greater than 9, where the module hierarchy changed substantially,
and using the [GHC.API][] makes it easier to support new versions of GHC when they are released.

### Fragile import strategy

```haskell
import Predicate
import TyCoRep

...

-- This will break if 'isEqPrimPred' is (re)moved or the import hierarchy changes.
foo :: Type -> Bool
foo = isEqPrimPred
```

### Recommended import strategy

```haskell
import qualified Language.Haskell.Liquid.GHC.API as GHC

...

foo :: GHC.Type -> Bool
foo = GHC.isEqPrimPred -- OK.
```


# FAQs

## A new version of GHC is out. How do I support it?

Typically the first thing you might want to do is to run a "clean" `cabal v2-build` or `stack build` using
the latest compiler and "check the damage". If you are lucky, everything works out of the box, otherwise
compilation might fail with an error, typically because some `ghc` API function has been removed/moved/renamed.
The way to fix it is to modify the [GHC.API][] shim module and perform any required change, likely by 
conditionally compiling some code in a `CPP` block. For minor changes, it's usually enough to perform small
changes, but for more tricky migrations it might be necessary to backport some GHC code, or create some
patter synonym to deal with changes in type constructors. You can see an example of this technique in
action by looking at the pattern synonym for [FunTy][].

## Is there a way to run the testsuite for different versions of GHC?

Yes. The easiest way is to run one of the scripts inside the `scripts/test` directory. We provide scripts
to run the testsuite for a variety of GHC versions, mostly using `stack` but also with `cabal` (e.g.
`test_810_plugin.sh`). If run without arguments, the script will run the _full_ testsuite. If an argument
is given, only a particular pattern/test will be run. Running

```
./scripts/test/test_810_plugin.sh BST
```

will run all the tests which name matches "BST". In case the "fast recompilation" is desired, it's totally
possibly to pass `LIQUID_DEV_MODE` to the script, for example:

```
LIQUID_DEV_MODE=true ./scripts/test/test_810_plugin.sh
```

[GHC.API]: https://github.com/ucsd-progsys/liquidhaskell/blob/develop/src/Language/Haskell/Liquid/GHC/API.hs
[FunTy]: https://github.com/ucsd-progsys/liquidhaskell/blob/develop/src/Language/Haskell/Liquid/GHC/API.hs#L224
