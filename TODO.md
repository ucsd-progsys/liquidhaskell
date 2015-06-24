# TODO

## cutsolver

Goal, be able to acyclic kvars without QUALIFIERS e.g.

+ implement solver
+ run on all benchmarks :)

## stats

+ How many *different* binders is each kvar bound to in constraints?

## non-trivial-sorts

+ partition sorts into non-trivial refinements

+ replace all "$k" for trivial sorts

     type Trivial = TrivialSort | NonTrivialSort  
     type TrivialMap = Map Sort Trivial  
     mkTrivialMap :: FInfo a -> TrivialMap
     simplifyTrivial :: FInfo a -> TrivialMap -> FInfo a
     simplify :: FInfo a -> FInfo a
