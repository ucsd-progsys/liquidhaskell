TODO
====

cutsolver
---------

Goal, be able to acyclic kvars without QUALIFIERS e.g.

1. write test for loop-free constraint
2. implement solver
3. write test for loop-y constraints
4. find "cut" kvars
5. implement solver
6. run on all benchmarks :)


stats
-----

A. Decompose constraints into independent pieces.
   How big is each component?

   - compute kv-read-write graph
   - label edge by constraint
   - compute CONNECTED COMPONENT
   - partition
 
B. How many *different* binders is each kvar bound to in constraints?


### Component Size
stats.

