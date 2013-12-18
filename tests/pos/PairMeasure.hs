module Foo where

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}

{-@ type Pair a b   = {vvv : ({v:a | v = (getfst vvv)}, b) | true } @-}
{-@ type OPList a b = [(Pair a b)]<\h -> {v: (Pair a b) | (getfst v) >= (getfst h)}> @-}
{-@ type OList a    = [a]<\hhh -> {vvvv: a | (vvvv >= hhh)}> @-}

{-@ getFsts          :: OPList a b -> OList a @-}
getFsts []           = [] 
getFsts ((x,_) : xs) = x : getFsts xs



