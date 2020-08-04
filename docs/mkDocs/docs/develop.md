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

 - To update the `liquid-fixpoint` submodule, run

    ```
    cd ./liquid-fixpoint
    git fetch --all
    git checkout <remote>/<branch>
    cd ..
    ```

   This will update `liquid-fixpoint` to the latest version on `<branch>`
   (usually `master`) from `<remote>` (usually `origin`).

 - After updating `liquid-fixpoint`, make sure to include this change in a
   commit! Running

    ```
    git add ./liquid-fixpoint
    ```

   will save the current commit hash of `liquid-fixpoint` in your next commit
   to the `liquidhaskell` repository.

 - For the best experience, **don't** make changes directly to the
   `./liquid-fixpoint` submodule, or else git may get confused. Do any
   `liquid-fixpoint` development inside a separate clone/copy elsewhere.

 - If something goes wrong, run

    ```
    rm -r ./liquid-fixpoint
    git submodule update --init
    ```

   to blow away your copy of the `liquid-fixpoint` submodule and revert to the
   last saved commit hash.

 - Want to work fully offline? git lets you add a local directory as a remote.
   Run

    ```
    cd ./liquid-fixpoint
    git remote add local /path/to/your/fixpoint/clone
    cd ..
    ```

   Then to update the submodule from your local clone, you can run

    ```
    cd ./liquid-fixpoint
    git fetch local
    git checkout local/<branch>
    cd ..
    ```


## Generating Performance Reports

**DEPRECATED**

We have set up infrastructure to generate performance reports using [Gipeda](https://github.com/nomeata/gipeda).

Gipeda will generate a static webpage that tracks the performance improvements
and regressions between commits. To generate the site, first ensure you have the
following dependencies available:

* Git
* Cabal >= 1.18
* GHC
* Make
* Bash (installed at `/bin/bash`)

After ensuring all dependencies are available, from the Liquid Haskell
directory, execute:

    cd scripts/performance
    ./deploy-gipeda.bash

This will download and install all the relevant repositories and files. Next, to
generate the performance report, use the `generate-site.bash` script. This script
has a few options:

* `-s [hash]`: Do not attempt to generate performance reports for any commit
older than the commit specified by the entered git hash
* `-e [hash]`: Do not attempt to generate performance reports for any commit
newer than the commit specified by the entered git hash
* `-f`: The default behavior of `generate-site.bash` is to first check if logs
have been created for a given hash. If logs already exist, `generate-site.bash`
will not recreate them. Specify this option to skip this check and regenerate
all logs.

You should expect this process to take a very long time. `generate-site.bash`
will compile each commit, then run the entire test suite and benchmark suite
for each commit. It is suggested to provide a manageable range to `generate-site.bash`:

    ./generate-site.bash -s [starting hash] -e [ending hash]

...will generate reports for all commits between (inclusive) [starting hash]
and [ending hash].

    ./generate-site.bash -s [starting hash]

... will generate reports for all commits newer than [starting hash]. This command
can be the basis for some automated report generation process (i.e. a cron job).

Finally, to remove the Gipeda infrastructure from your computer, you may execute:

    ./cleanup-gipeda.bash

...which will remove any files created by `deploy-gipeda.bash` and `generate-site.bash`
from your computer.


## Configuration Management

It is very important that the version of Liquid Haskell be maintained properly.

Suppose that the current version of Liquid Haskell is `A.B.C.D`:

+ After a release to hackage is made, if any of the components `B`, `C`, or `D` are missing, they shall be added and set to `0`. Then the `D` component of Liquid Haskell shall be incremented by `1`. The version of Liquid Haskell is now `A.B.C.(D + 1)`

+ The first time a new function or type is exported from Liquid Haskell, if any of the components `B`, or `C` are missing, they shall be added and set to `0`. Then the `C` component shall be incremented by `1`, and the `D` component shall stripped. The version of Liquid Haskell is now `A.B.(C + 1)`

+ The first time the signature of an exported function or type is changed, or an exported function or type is removed (this includes functions or types that Liquid Haskell re-exports from its own dependencies), if the `B` component is missing, it shall be added and set to `0`. Then the `B` component shall be incremented by `1`, and the `C` and `D` components shall be stripped. The version of Liquid Haskell is now `A.(B + 1)`

+ The `A` component shall be updated at the sole discretion of the project owners.

## Updating GHC Versions

Here's a script to generate the diff for the `desugar` modules.

```
export GHCSRC=$HOME/Documents/ghc

# Checkout GHC-8.2.2
(cd $GHCSRC && git checkout ghc-8.2.2 && git pull)

# make a patch
diff -ur $GHCSRC/compiler/deSugar src/Language/Haskell/Liquid/Desugar > liquid.patch

# Checkout GHC-8.4.3
(cd $GHCSRC && git checkout ghc-8.2.2 && git pull)

# Copy GHC desugarer to temporary directory
cp -r $GHCSRC/compiler/deSugar .

# Patch
(cd deSugar && patch -p5 --merge --ignore-whitespace < ../liquid.patch)

# Copy stuff over
for i in src/Language/Haskell/Liquid/Desugar/*.*; do j=$(basename $i); echo $j; cp deSugar/$j src/Language/Haskell/Liquid/Desugar; done
```

Here's the magic diff that we did at some point that we keep bumping up to new GHC versions:

https://github.com/ucsd-progsys/liquidhaskell/commit/d380018850297b8f1878c33d0e4c586a1fddc2b8#diff-3644b76a8e6b3405f5492d8194da3874R224 

[compiler plugin]: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/extending_ghc.html#compiler-plugins

## Releasing on Hackage

*NOTE: The following section is relevant only for few developers, i.e. the ones which are directly involved
in the release process. Most contributors can skip this section.*

We provide a conveniency script to upload all the `liquid-*` packages (**including** `liquid-fixpoint`) on
Hackage, in a lockstep fashion. To do so, it's possible to simply run the `scripts/release_to_hackage.sh`
Bash script. The script tries to determine the packages to upload by scanning the $PWD for packages named
appropriately. It will ask the user for confirmation before proceeding, and `cabal upload` will be used
under the hood. Any options passed to the script will be routed to `cabal`. For example, to upload a package
using a particular combination of user and password:

```
./scripts/release_to_hackage.sh -u foo -p bar
```
