Dependent Types
----------------

- Check user defined sort is the same as Haskell sort. 
  Now user defined sort is ignored after parsing. 







Equational Reasoning 
--------------------


- look at isabelle's lambda lifting 
- http://www.concrete-semantics.org/concrete-semantics.pdf
- http://www.mimuw.edu.pl/~lukaszcz/combs.pdf

HERE HERE BACK TO LOGIC!!!! No need for defunc this time!

tests 
  - [OK] AppendArrow 
  - [OK] MapAppend
  - [OK] MapFusion
  - [OK] ConcatMap
  - [OK] Monadic Laws for Lists 
  - Associativity of Monadic Laws 
      - allow functions
      - proove it by hand



TODO: what if multiple arguments appear many times?



Other: 
  - when I cannot prove stuff I need a time out
  - Go to next example!


Efficiency: 
  - reuse all the SMT/logic info



- DONE  
  - Reduce terms because for example, term append N N appears. 
  - add constructor info in unfolding (used for the followng)
  - make sure recursive calls happen only to smaller inputs
  - Create Haskell expression that is equivalent to the sufficient axioms and 
      - replace the call to auto
  - I create a combineproofs variable that combines proofs. Right now its type is true 
    and everything works. Add abstract refinements to make a more concrete type if something breaks!
 
examples:
  - map reduce
  - monadic laws
  - interpreter
  - solver
  - hlint
  - pipes
  - list reversing?


  

-- autoEq ::x:a -> y:a -> {v:a | v == y && x == y }

{-

step e (e1 == e2)

<==>

autoEq e1 e2

<==>

auto (e1 == e && e == e2)
-}
