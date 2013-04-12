module Foo where

{-@ measure fst :: (a, b) -> a 
    fst (x, y) = x
  @-}

{-@ type OPList a b = [(a, b)]<\h -> {v: (a, b) | (fst v) >= (fst h)}> @-}

{-@ type OList a    = [a]<\h -> {v: a | (v >= h)}> @-}


{-@ getFsts          :: OPList a b -> OList a @-}

getFsts []           = [] 
getFsts ((x,_) : xs) = x : getFsts xs

