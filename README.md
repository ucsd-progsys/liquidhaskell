Liquid Fixpoint [![Build Status](https://travis-ci.org/ucsd-progsys/liquid-fixpoint.svg?branch=master)](https://travis-ci.org/ucsd-progsys/liquid-fixpoint)
===============

This package is a Haskell wrapper to the SMTLIB-based
Horn-Clause/Logical Implication constraint solver used
for Liquid Types.

The solver itself is written in Ocaml.

The package includes:

1. Types for Expressions, Predicates, Constraints, Solutions
2. Code for serializing the above
3. Code for parsing the results from the fixpoint.native binary
4. The Ocaml fixpoint code and pre-compiled binaries
5. (Deprecated) Z3 binaries if you want to link against the API.

Requirements
------------

In addition to the .cabal dependencies you require

- A Z3 (<http://z3.codeplex.com>) or CVC4 (<http://cvc4.cs.nyu.edu>) binary.
  If on Windows, please make sure to place the binary and any associated DLLs
  in your "cabal/bin" folder, right next to the fixpoint.native.exe binary.

- An ocaml compiler (if installing with -fbuild-external).

How To Build and Install
------------------------

    cabal install

Using SMTLIB-based SMT Solvers
------------------------------

You can use one of several SMTLIB2 compliant solvers, by:

    fixpoint --smtsolver=z3 path/to/file.hs

Currently, we support

    * z3
    * CVC4
    * MathSat

Building With Z3 (Optional)
---------------------------

As of now, you can **ONLY link with Z3 on Linux**

These other things are required

- the GNU multiprecision library
- a recent OCaml compiler
- the CamlIDL library

1. Install the above on a recent Linux by

    sudo apt-get install haskell-platform ocaml camlidl g++ libgmp3c2

2. Modify `configure` to set

    Z3MEM=true

3. Install as usual

    cabal install

How to Clone
------------

To clone Liquid Fixpoint:

git clone git@github.com:ucsd-progsys/liquid-fixpoint.git

Configuration Management
------------------------

It is very important that the version of Liquid Fixpoint be maintained properly.

Suppose that the current version of Liquid Haskell is `A.B.C.D`:

+ After a release to hackage is made, if any of the components `B`, `C`, or `D` are missing, they shall be added and set to `0`. Then the `D` component of Liquid Fixpoint shall be incremented by `1`. The version of Liquid Fixpoint is now `A.B.C.(D + 1)`

+ The first time a new function or type is exported from Liquid Fixpoint, if any of the components `B`, or `C` are missing, they shall be added and set to `0`. Then the `C` component shall be incremented by `1`, and the `D` component shall stripped. The version of Liquid Fixpoint is now `A.B.(C + 1)`

+ The first time the signature of an exported function or type is changed, or an exported function or type is removed (this includes functions or types that Liquid Fixpoint re-exports from its own dependencies), if the `B` component is missing, it shall be added and set to `0`. Then the `B` component shall be incremented by `1`, and the `C` and `D` components shall be stripped. The version of Liquid Fixpoint is now `A.(B + 1)`

+ The `A` component shall be updated at the sole discretion of the project owners.

It is recommended to use the [Bumper](https://hackage.haskell.org/package/bumper) utility to manage the versioning of Liquid Fixpoint. Bumper will automatically do the correct update to the cabal file. Additionally, it will update any packages that you have the source for that depend on Liquid Fixpoint.

To update Liquid Fixpoint and Liquid Haskell, first clone Liquid Haskell and Liquid Fixpoint to a common location:

```
git clone https://github.com/ucsd-progsys/liquidhaskell.git
git clone https://github.com/ucsd-progsys/liquid-fixpoint.git
```

To increment the `D` component of Liquid Fixpoint:

```
./path/to/bumper -3 liquid-fixpoint
```

This will update the `D` component of Liquid Fixpoint. If necessary, this will update the `Build-Depends` of Liquid Haskell. If the `Build-Depends` was updated, Liquid Haskell's `D` component will be incremented.

To increment the `C` component of Liquid Fixpoint, and strip the `D` component:

```
./path/to/bumper --minor liquid-fixpoint
```

As before, this will update Liquid Fixpoint and, if necessary, Liquid Haskell.

To increment the `B` component of Liquid Fixpoint, and strip the `D` and `C` components:

```
./path/to/bumper --major liquid-fixpoint
```

As before, this will update Liquid Fixpoint and, if necessary, Liquid Haskell

SMTLIB2 Interface
-----------------

There is a new SMTLIB2 interface directly from Haskell:

+ Language.Fixpoint.SmtLib2

See `tests/smt2/{Smt.hs, foo.smt2}` for an example of how to use it.

Options
-------

`--native` runs the **highly experimental** native solver.

`--parts` Partitions an `FInfo` into a `[FInfo]` and emits a bunch of files. So:

    $ fixpoint -n -p path/to/foo.fq

will now emit files:

    path/to/.liquid/foo.1.fq
    path/to/.liquid/foo.2.fq
    . . .
    path/to/.liquid/foo.k.fq

and also a dot file with the constraint dependency graph:

    path/to/.liquid/foo.fq.dot
