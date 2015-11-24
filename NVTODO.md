Equational Reasoning 
--------------------
Other: 
  - lists: reverse with and without accumulator are the same
  - Combine proofs in a robust way, now I use the imported `by`
  - make flag to run expProofs
  - Go to next example!


Efficiency: 
  - reuse all the SMT/logic info



- DONE  
  - Reduce terms because for example, term append N N appears. 
  - add constructor info in unfolding (used for the followng)
  - make sure recursive calls happen only to smaller inputs
  - Create Haskell expression that is equivalent to the sufficient axioms and 
      - replace the call to auto
 
examples:
  - map reduce
  - monadic laws
  - interpreter
  - solver
  - hlint
  - pipes