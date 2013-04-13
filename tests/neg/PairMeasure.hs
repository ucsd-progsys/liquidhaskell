module Foo where

{-@ measure fst :: (a, b) -> a 
    fst (x, y) = x
  @-}

{-@ type Pair a b   = {v0 : ({v:a | v = (fst v0)}, b) | true } @-}

{-@ type OPList a b = [(Pair a b)]<\h -> {v: (Pair a b) | (fst v) >= (fst h)}> @-}

{-@ type OList a    = [a]<\h -> {v: a | (v >= h)}> @-}

{-@ getFsts          :: OPList a b -> OList a @-}
getFsts []           = [] 
getFsts ((x,_) : xs) = x : getFsts xs

{-@ canary :: a -> {v:a | false} @-}
canary x = x 
