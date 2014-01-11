module Foo () where

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}

{-@ type Pair a b   = {v0 : ({v:a | v = (getfst v0)}, b) | true } @-}

{-@ type OPList a b = [(Pair a b)]<\h -> {v: (Pair a b) | (getfst v) >= (getfst h)}> @-}

{-@ type OList a    = [a]<\h -> {v: a | (v >= h)}> @-}

{-@ getFsts          :: OPList a b -> OList a @-}
getFsts []           = [] 
getFsts ((x,_) : xs) = x : getFsts xs

{-@ canary :: a -> {v:a | false} @-}
canary x = x 
