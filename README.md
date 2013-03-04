Liquid Fixpoint
===============

This package is a Haskell wrapper to the SMT (Z3) Based Horn-Clause/
Logical Implication constraint solver used for Liquid Types. The solver
itself is written in Ocaml. The Haskell Library contains

1. Types for representing Expressions, Predicates, Constraints, Solutions
2. Code for serializing the above 
3. Code for parsing the results from the fixpoint.native binary

Requirements
------------

The package include the Ocaml fixpoint code, as well as the z3 binaries

In addition to the .cabal dependencies, to build you must have

- a recent OCaml compiler
- the GNU multiprecision library
- the CamlIDL library

Due to the Z3 dependency, LiquidHaskell can **only be compiled on Linux** at the moment.

How to Clone
------------

To clone liquidhaskell:

    git clone git@github.com:ucsd-progsys/liquid-fixpoint.git

How To Build and Install
------------------------

    cabal install
