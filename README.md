![LiquidHaskell](/resources/logo.png)



[![Hackage](https://img.shields.io/hackage/v/liquidhaskell.svg)](https://hackage.haskell.org/package/liquidhaskell) [![Hackage-Deps](https://img.shields.io/hackage-deps/v/liquidhaskell.svg)](http://packdeps.haskellers.com/feed?needle=liquidhaskell) [![Build Status](https://img.shields.io/circleci/project/ucsd-progsys/liquidhaskell/master.svg)](https://circleci.com/gh/ucsd-progsys/liquidhaskell)
[![Windows build status](https://ci.appveyor.com/api/projects/status/78y7uusjcgor5p16/branch/develop?svg=true)](https://ci.appveyor.com/project/varosi/liquidhaskell-nlhra/branch/develop)

This is the **development** site of the LiquidHaskell formal verification tool.

If you're a LiquidHaskell **user** (or just curious), you probably want to go to [the documentation website](https://ucsd-progsys.github.io/liquidhaskell/) instead.

# Contributing

This is an open-source project, and we love getting feedback (and patches)!

## Reporting a Bug

If something doesn't work as it should, please consider opening a [github issue](https://github.com/ucsd-progsys/liquidhaskell/issues)
to let us know. If possible, try to:

* Try to use a descriptive title;
* State as clearly as possible what is the problem you are facing;
* Provide a small Haskell file producing the issue;
* Write down the expected behaviour vs the actual behaviour;
* If possible, let us know if you have used the [plugin](install.md) or the [executable](legacy.md) and
  which _GHC version_ you are using.

## Your first Pull Request

We are thrilled to get PRs! Please follow these guidelines, as doing so will increase the chances of 
having your PR accepted:

* The main LH repo [lives here](https://github.com/ucsd-progsys/liquidhaskell)
* Please create pull requests against the `develop` branch.
* Please be sure to include test cases that illustrate the effect of the PR
    - e.g. show new features that that are supported or how it fixes some previous issue
* If you're making user-visible changes, please also add documentation
    - e.g. [options.md](options.md), [specifications.md](specifications.md), the [main tutorial](https:///github.com/ucsd-progsys/intro-refinement-types) (as relevant)

Pull requests don't just have to be about code: documentation can often be improved too!

## Ask for Help

If you have further questions or you just need help, you can always reach out on our [slack channel](https://join.slack.com/t/liquidhaskell/shared_invite/enQtMjY4MTk3NDkwODE3LTFmZGFkNGEzYWRkNDJmZDQ0ZGU1MzBiZWZiZDhhNmY3YTJiMjUzYTRlNjMyZDk1NDU3ZGIxYzhlOTIzN2UxNWE), [google groups mailing list](https://groups.google.com/forum/#!forum/liquidhaskell), [GitHub issue tracker](https://github.com/ucsd-progsys/liquidhaskell/issues), or by emailing [Ranjit Jhala](https://github.com/ranjitjhala), [Niki Vazou](https://github.com/nikivazou).

# General Development Guide

For those diving into the implementation of LiquidHaskell, here are a few tips:

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

_For a way of running the test suite for multiple GHC versions, consult the General Development FAQs. below_

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

## How to create performance comparison charts

Everytime `liquidhaskell` tests are run, a report of the time taken by
each test is written to a file `tests/logs/<host>-<time>/summary.csv`.

There is a script `scripts/plot-performance/chart_perf.sh` that can be
used to generate comparison charts in `svg` and `png` formats. It
requires [gnuplot](http://www.gnuplot.info/) to run. The following
command will produce two files `perf.svg` and `perf.png` in the
current directory.

    $ scripts/plot-performance/chart_perf.sh path_to_before_summary.csv path_to_after_summary.csv

The current formatting is optmized for comparing the outputs of running
the benchmarks alone.

    $ scripts/test/test_810.sh Benchmarks

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

We provide a convenience script to upload all the `liquid-*` packages (**including** `liquid-fixpoint`) on
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

# GHC Plugin Development Guide

This code commentary describes the current architecture for the GHC [Plugin][] that enables LiquidHaskell
to check files as part of the normal compilation process. For the sake of this commentary, we refer to
the code provided as part of the `release/0.8.10.2` branch, commit `9a2f8284c5fe5b18ed0410e842acd3329a629a6b`.

## GHC.Interface vs GHC.Plugin

The module [GHC.Plugin][] is the main entrypoint for all the plugin functionalities. Whenever possible, this
module is reusing common functionalities from the [GHC.Interface][], which is the original module used to
interface LH with the old executable. Generally speaking, the [GHC.Interface][] module is considered "legacy"
and it's rarely what one wants to modify. It will probably be removed once the old executable stops being
supported, with the functions now in use by the [GHC.Plugin][] being moved into the latter.

## The GhcMonadLike shim

Part of the tension in designing the plugin was trying to reuse as much code as possible from the original
[GHC.Interface][] shipped with LiquidHaskell. Unfortunately this was not possible from the get-go due to the
fact most of the functions provided by that module were requiring a [GhcMonad][] constraint or usually
living in the [Ghc monad][], which is also the only concrete type which derives an instance for [GhcMonad][].
While we could have run each and every function with `runGhc`, this was not very satisfactory due to the
fact running the `Ghc` monad is fairly expensive as it requires a bit of extra state in order to run it.

However, most of the functions used by the [Ghc.Interface][] didn't require anything specific from the
underlying [Ghc monad][] if not access to the [HscEnv][] and the ability to grab the [DynFlags][], as well
as doing `IO`. Therefore, the [GhcMonadLike][] shim was born with the intent of replicating some of the
functions used by the [GHC.Interface][] but crucially making those polymorphic in a generic [GhcMonadLike][]
for which we can give instances for `CoreM`, `TcM` etc. We can do this because we do not require the extra
`ExceptionMonad` constraint and we do not require to implement `setHscEnv`.

This allowed us to change ever so slightly the functions provided by the [GHC.Interface][], expose them and
reuse them in the [Plugin][] module.

## Plugin architecture

Broadly speaking, the Plugin is organised this way: In the [typechecking phase][], we typecheck and desugar
each module via the GHC API in order to extract the unoptimised [core binds][] that are needed by
LH to work correctly. This is due to a tension in the design space; from one side LH needs access to the
"raw" core binds (binds where primitives types are not unboxed in the presence of a PRAGMA annotation,
for example) but yet the user can specify any arbitrary optimisation settings during compilation and we do
not want to betray the principle of least expectation by silently compiling the code with `-O0`. Practically
speaking, this introduces some overhead and is far from ideal, but for now it allows us to iterate quickly.
This phase is also responsible for:

* Extracting the [BareSpec][]s associated to any of the dependent modules;
* Producing the [LiftedSpec][] for the currently-compiled module;
* Storing the [LiftedSpec][] into an interface annotation for later retrieval;
* Checking and verifying the module using LH's existing API.

The reason why we do everything in the [typechecking phase][] is also to allow integrations with tools like
[ghcide][]. There are a number of differences between the plugin and the operations performed as part of the
[GHC.Interface][], which we are going to outline in the next section.

## Differences with the GHC.Interface

- The [GHC.Interface][] pre-processes the input files and calls into [configureGhcTargets][] trying to
  build a dependency graph by discovering dependencies the target files might require. Then, from this
  list any file in the include directory is filtered out, as well as any module which has
  a "fresh" `.bspec` file on disk, to save time during checking. In the [GHC.Plugin][] module though
  we don't do this and for us, essentially, each input file is considered a target, where we exploit the
  fact GHC will skip recompilation if unnecessary. This also implies that while the [GHC.Interface][] calls
  into [processTargetModule][] only for target files, the [GHC.Plugin][] has a single, flat function simply
  called [processModule][] that essentially does the same as `GHC.Interface.processModule` and
  `GHC.Interface.processTargetModule` fused together.

- While the [GHC.Interface][] sometimes "assembles" a [BareSpec][] by `mappend`ing the `commSpec` (i.e. comment spec)
  with the [LiftedSpec][] fetched from disk, if any, the Plugin doesn't do this but rather piggybacks on the
  [SpecFinder][] (described later) to fetch dependencies' specs.

- There is a difference in how we process LIQUID pragmas. In particular, for the executable they seems to
  be accumulated "in bulk" i.e. if we are refining a *target* module `A` that depends on `B`, `B` seems to
  inherit whichever flags we were using in the *target* module `A`. Conversely, the source plugin is "stateless"
  when it comes to LIQUID options, i.e. it doesn't have memory of _past_ options, what it counts when compiling
  a module `B` is the _global_ options and _any_ option this module defines. The analogy is exactly the
  same as with GHC language extensions, they have either global scope (i.e. `default-extensions` in the
  cabal manifest) or local scope (i.e. `{-# LANGUAGE ... #-}`).

## Finding specs for existing modules

This is all done by a specialised module called the [SpecFinder][]. The main exported function is
[findRelevantSpecs][] which, given a list of `Module`s, tries to retrieve the `LiftedSpec`s associated with
them. Typically this is done by looking into the interface files of the input modules, trying to deserialise
any `LiftedSpec` from the interface file's annotations.

# General Development FAQs

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

# GHC Plugin Development FAQs

## Is it possible that the behaviour of the old executable and the new / the plugin differ?

It might happen, yes, but the surface area is fairly small. Both modules work by producing a [TargetSrc][]
that is passed to the internal LH API, which is shared by _both_ modules. Therefore, any difference in 
behaviour has to be researched in the code path that produces such [TargetSrc][]. For the [GHC.Plugin][] this
happens in the `makeTargetSrc`, whereas for the [GHC.Interface][] this happens inside the [makeGhcSrc][] function.

## Why is the GHC.Interface using slightly different types than the GHC.Plugin module?

Mostly for backward-compatibility and for historical reasons. Types like [BareSpec][] used to be type alias
rather than `newtype`s, and things were slightly renamed to reflect better purpose when the support for the
plugin was added. While doing so we also added a compatibility layer in the form of some `optics` that can be used
to map back and forth (sometimes in a partial way) between old and new data structures. When in doubt,
**consider the GHC.Plugin as the single source of truth, and prefer whichever data structure the latter is
using**.


[Plugin]:              https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs
[GHC.Plugin]:          https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs
[GHC.Interface]:       https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Interface.hs
[SpecFinder]:          https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs
[BareSpec]:            https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/Types/Specs.hs#L301
[LiftedSpec]:          https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/Types/Specs.hs#L476
[TargetSrc]:           https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/Types/Specs.hs#L160
[Ghc monad]:           https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:Ghc
[HscEnv]:              https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:HscEnv
[DynFlags]:            https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:DynFlags
[GhcMonad]:            https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:GhcMonad
[GhcMonadLike]:        https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/GhcMonadLike.hs
[typechecking phase]:  https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs#L196-L224
[ghcide]:              https://github.com/haskell/ghcide
[findRelevantSpecs]:   https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs#L61
[core binds]:          https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html#t:CoreBind
[configureGhcTargets]: https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Interface.hs#L268
[processTargetModule]: https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Interface.hs#L468
[processModule]:       https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs#L393

