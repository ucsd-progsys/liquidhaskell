Liquid Fixpoint
===============

This package is a Haskell wrapper to the SMTLIB-based 
Horn-Clause/Logical Implication constraint solver used
for Liquid Types. 

The solver itself is written in Ocaml. 

The package includes: 

1. Types for Expressions, Predicates, Constraints, Solutions
2. Code for serializing the above 
3. Code for parsing the results from the fixpoint.native binary
4. The Ocaml fixpoint code
5. (Deprecated) Z3 binaries if you want to link against the API.

Requirements
------------

In addition to the .cabal dependencies you require 

- Recent Ocaml compiler

One of:

- [Z3 Binary](http://z3.codeplex.com/) Version >= 4.3.2

Make sure that the `z3` executable is available on your $PATH

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

To clone liquidhaskell:

    git clone git@github.com:ucsd-progsys/liquid-fixpoint.git

SMTLIB2 Interface
-----------------

There is a new SMTLIB2 interface directly from Haskell:

+ Language.Fixpoint.SmtLib2

See `tests/smt2/{Smt.hs, foo.smt2}` for an example of how to use it.
