#!/bin/bash

FIXPOINT=/home/rjhala/research/liquidhaskell/external/fixpoint/fixpoint.native
Z3=/home/rjhala/research/liquidhaskell/external/z3/bin/z3

for f in $1/*.fq; do 
  echo "Processing $f ..."; 
  $FIXPOINT -smtlib $f -out $f.smt 
  perl -pi -e 's/#/_/g' $f.smt
  $Z3 $f.smt
done

