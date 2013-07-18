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

- the GNU multiprecision library 
- a recent OCaml compiler
- the CamlIDL library

Due to the Z3 dependency, LiquidHaskell can **only be compiled on Linux** at the moment.

The above can be carried out in one shot on a recent Linux by

    sudo apt-get install haskell-platform ocaml camlidl g++ libgmp3c2


How to Clone
------------

To clone liquidhaskell:

    git clone git@github.com:ucsd-progsys/liquid-fixpoint.git

How To Build and Install
------------------------

    cabal install


TpGen
=====

1. command line option to fixpoint.native
    
    a. -smtlib = ref (SMTLIB option)
    b. tpNull 
    
    fixpoint.native -smt z3    foo.fq
    fixpoint.native -smt yices foo.fq
    fixpoint.native -smt cvc4  foo.fq

    (default: smtZ3)


2. liquid-fixpoint cmdArgs

    fixpoint -smt z3
    fixpoint -smt yices 
    fixpoint -smt cvc4

3. liquid-fixpoint check if solver exists

4. liquid cmdArgs
    
    liquid -smt z3 etc.

5. Install yices
    - run benchmarks

6. Install cvc4 
    - run benchmarks

7. Install mathsat5
    - run benchmarks

8. Add set axioms
    - redo 5,6,7

9. MERGE

10. Find clean platform-independent BUILD.

    DELETE z3bind (easy build on macOS) 
   



Failed 18 tests:
 
  Broken:
    , SS.hs, cont.hs, ptr.hs, ptr2.hs, ptr3.hs
   
  Sets:
    , deepmeas0.hs
    , ListConcat.hs
    , ListElem.hs
    , listSet.hs
    , listSetDemo.hs
    , stacks0.hs
    , zipper.hs
    , zipper0.hs
    , meas9.hs
    , meas10.hs
    , meas11.hs
 





