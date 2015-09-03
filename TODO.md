# TODO


Trace: [DISCARDING] : [208, 84, 85, 55, 60]

Trace: [DISCARDING] : [80, 6, 86, 7, 9, 10, 74]

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
