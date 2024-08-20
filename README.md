![LiquidHaskell](/resources/logo.png)


[![Hackage](https://img.shields.io/hackage/v/liquidhaskell.svg)](https://hackage.haskell.org/package/liquidhaskell) [![Hackage-Deps](https://img.shields.io/hackage-deps/v/liquidhaskell.svg)](http://packdeps.haskellers.com/feed?needle=liquidhaskell) [![Build Status](https://img.shields.io/circleci/project/ucsd-progsys/liquidhaskell/master.svg)](https://circleci.com/gh/ucsd-progsys/liquidhaskell)

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
* Please, let us know which liquidhaskell version you are using.

## Your first Pull Request

We are thrilled to get PRs! Please follow these guidelines, as doing so will increase the chances of
having your PR accepted:

* The main LH repo [lives here](https://github.com/ucsd-progsys/liquidhaskell)
* Please create pull requests against the `develop` branch.
* Please be sure to include test cases that illustrate the effect of the PR
    - e.g. show new features that that are supported or how it fixes some previous issue
* If you're making user-visible changes, please also add documentation
    - e.g. [options.md](docs/mkDocs/docs/options.md), [specifications.md](docs/mkDocs/docs/specifications.md), the [main tutorial](https:///github.com/ucsd-progsys/intro-refinement-types) (as relevant)

Pull requests don't just have to be about code: documentation can often be improved too!

## Ask for Help

If you have further questions or you just need help, you can always reach out on our [slack channel](https://join.slack.com/t/liquidhaskell/shared_invite/enQtMjY4MTk3NDkwODE3LTFmZGFkNGEzYWRkNDJmZDQ0ZGU1MzBiZWZiZDhhNmY3YTJiMjUzYTRlNjMyZDk1NDU3ZGIxYzhlOTIzN2UxNWE), [google groups mailing list](https://groups.google.com/forum/#!forum/liquidhaskell), [GitHub issue tracker](https://github.com/ucsd-progsys/liquidhaskell/issues), or by emailing [Ranjit Jhala](https://github.com/ranjitjhala), [Niki Vazou](https://github.com/nikivazou).

# General Development Guide

For those diving into the implementation of LiquidHaskell, here are a few tips:

## Running the pluging on individual files

```
cabal build liquidhaskell
cabal exec ghc -- -fplugin=LiquidHaskell FILE.hs
```

## Building

### Cabal

```
cabal build
```

### Faster recompilation

When changing the `liquidhaskell-boot` library, sometimes we don't want
to rebuild `liquidhaskell` or `liquid-vector` when testing the changes.
In these cases we can set the environment variable `LIQUID_DEV_MODE=true`
when running `cabal` to skip rebuilding those packages.

DANGER: Note that this can give an invalid result if the changes to
`liquidhaskell-boot` do require rebuilding other `liquid*` packages.

## How To Run Regression Tests

For documentation on the `test-driver` executable itself, please refer to the
`README.md` in `tests/` or run `cabal run tests:test-driver -- --help`

You can run *all* the tests by

    $ ./scripts/test/test_plugin.sh

You can run a bunch of particular test-groups instead by

    $ ./scripts/test/test_plugin.sh <test-group-name1> <test-group-name2> ...

and you can list all the possible test options with

    $ ./scripts/test/test_plugin.sh --help

or get a list of just the test groups, one per line, with

    $ ./scripts/test/test_plugin.sh --show-all

To pass in specific parameters, you can invoke cabal directly with

    $ cabal build tests:<test-group-name> --ghc-options=-fplugin-opt=LiquidHaskell:--no-termination

For example:

    $ cabal build tests:unit-neg --ghc-options=-fplugin-opt=LiquidHaskell:--no-termination

Or your favorite number of threads, depending on cores etc.

You can directly extend and run the tests by modifying the files in

    tests/harness/

### Parallelism in Tests

Tests run in parallel, unless the flag `--measure-timings` is specified to `test_plugin.sh`.

## How to create performance comparison charts

When `liquidhaskell` tests run, we can collect timing information with

    $ ./scripts/test/test_plugin.sh --measure-timings

Measures will be collected in `.dump-timings` files under `dist-newstyle` directory. These can be
converted to json data with

```bash
cabal v2-build ghc-timings
cabal v2-exec ghc-timings dist-newstyle
```

which will produce `tmp/*.json` files.

Then a csv report can be generated from this json files with
```
cabal v2-run benchmark-timings -- tmp/*.json --phase LiquidHaskell -o summary.csv
```
On each line, the report will contain the time taken by each test.

Comparison charts in `svg` format can be generated by invoking

```
cabal v2-run plot-performance -- -b path_to_before_summary.csv -a path_to_after_summary.csv -s 50 -f "benchmark"
```

This will generate three files `filtered.svg` (a subset of tests with a `benchmark` prefix, enabled by the `-f` option),
`top.svg` and `bot.svg` (top 50 speedups and slowdowns over the entire test set, both enabled by the `-s` option) in the
current directory. The `-f` and `-s` options can be used/omitted independently. If both are omitted, a single `perf.svg`
will be produced covering the full input test set. Additionally, their effects can be combined by providing a third `-c`
option (this  will produce 2 files `filtered-top.svg` and `filtered-bot.svg` instead of 3). An optional key `-o` can be
supplied to specify an output directory for the generated files.

There is also a legacy script `scripts/plot-performance/chart_perf.sh` that can be used to generate comparison charts
in both `svg` and `png` formats. It requires [gnuplot](http://www.gnuplot.info/) to run and assumes both files contain
the same test set. The following command will produce two files `perf.svg` and `perf.png` in the current directory.

    $ scripts/plot-performance/chart_perf.sh path_to_before_summary.csv path_to_after_summary.csv

The current formatting is optimized for comparing some subsets of the full test run, typically just the benchmarks alone.
If one wishes to save time or is not interested in top speedups/slowdowns, the benchmark subset can be obtained by running

    $ scripts/test/test_plugin.sh \
        benchmark-stitch-lh \
        benchmark-bytestring \
        benchmark-vector-algorithms \
        benchmark-cse230 \
        benchmark-esop2013 \
        benchmark-icfp15-pos \
        benchmark-icfp15-neg

## Miscelaneous tasks

* **Profiling** See the instructions in [scripts/profiling-driver/ProfilingDriver.hs](scripts/profiling-driver/ProfilingDriver.hs).
* **Getting stack traces on exceptions** See `-xc` flag in the [GHC user's guide][ghc-users-guide].
* **Working with submodules** See `man gitsubmodules` or the [git documentation site][git-documentation].

[ghc-users-guide]: https://downloads.haskell.org/ghc/latest/docs/users_guide/
[git-documentation]: https://git-scm.com/doc

## GHC support policy

LH supports only one version of GHC at any given time. This is because LH depends heavily on the `ghc` library
and there is currently no distinction between public API's and API's internal to GHC. There are currently no
release notes for the `ghc` library and breaking changes happen without notice and without deprecation
periods. Supporting only one GHC version saves developer time because it obviates the need for `#ifdef`'s
throughout the codebase, or for an compatibility layer that becomes increasingly difficult to write as we
attempt to support more GHC versions. Porting to newer GHC versions takes less time, the code is easier to
read and there is less code duplication.

Users of older versions of GHC can still use older versions of LH.

## The GHC.API module

In order to minimize the effort in porting LH to new releases of GHC, we need a way to abstract over breaking
changes in the `ghc` library, which might change substantially with every major GHC release. This is
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
and it's rarely what one wants to modify. It will probably be removed at some point.

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

Typically the first thing you might want to do is to run a "clean" `cabal build` using
the latest compiler and "check the damage". If you are lucky, everything works out of the box, otherwise
compilation might fail with an error, typically because some `ghc` API function has been removed/moved/renamed.
The way to fix it is to modify the [GHC.API][] shim module and perform any required change, likely by
conditionally compiling some code in a `CPP` block. For minor changes, it's usually enough to perform small
changes, but for more tricky migrations it might be necessary to backport some GHC code, or create some
patter synonym to deal with changes in type constructors.

## Is there a way to run the testsuite for different versions of GHC?

Currently, no. Only one version of GHC is supported and that is the one
that can be tested with `./scripts/test/test_plugin.sh`.

[GHC.API]:             liquidhaskell-boot/src-ghc/Liquid/GHC/API.hs
[Plugin]:              liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin.hs
[GHC.Plugin]:          liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin.hs
[GHC.Interface]:       liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Interface.hs
[SpecFinder]:          liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs
[LiftedSpec]:          liquidhaskell-boot/src/Language/Haskell/Liquid/Types/Specs.hs#L559
[TargetSrc]:           liquidhaskell-boot/src/Language/Haskell/Liquid/Types/Specs.hs#L158
[typechecking phase]:  liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin.hs#L211-L226
[ghcide]:              https://github.com/haskell/ghcide
[findRelevantSpecs]:   liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs#L65
[core binds]:          https://hackage.haskell.org/package/ghc-9.6.3/docs/GHC-Core.html#t:CoreBind
[configureGhcTargets]: liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Interface.hs#L254
[processTargetModule]: liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Interface.hs#L483
[processModule]:       liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin.hs#L509

