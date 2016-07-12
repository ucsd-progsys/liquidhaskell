{- This fails with the error:

```
 /Users/rjhala/research/stack/liquidhaskell/tests/todo/T771.hs:7:13: Error: Bad Type Specification
 Wrenn.incr :: (Num a) => a -> {VV : a | VV == thing}
     Sort Error in Refinement: {VV : a_amT | VV == thing}
     Unbound Symbol thing
```

which is accurate, but misleading, as the *real* problem is you can't have
binders on typeclass constraints.

-}

module Wrenn where

{-@ incr :: thing:(Num a) => a -> {v:a | v = thing} @-}

incr :: (Num a) => a -> a
incr x = x
