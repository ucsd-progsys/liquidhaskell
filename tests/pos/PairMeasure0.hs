module Foo () where

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}

{-@ type Pair a b   = {v0 : ({v:a | v = (getfst v0)}, b) | true } @-}
{-@ type OPList a b = [(Pair a b)]<\h -> {v: (Pair a b) | (getfst v) >= (getfst h)}> @-}
{-@ type OList a    = [a]<\h -> {v: a | (v >= h)}> @-}


-- This is Unsafe, as refinements in Predicate parameters (i.e., Pair a b)
-- are lost, so application `getFsts` cannot be proven safe
{-@ getFsts          :: OPList a b -> OList a @-}
getFsts :: [(a, b)] -> [a]
getFsts []           = [] 
getFsts ((x,_) : xs) = x : getFsts xs



