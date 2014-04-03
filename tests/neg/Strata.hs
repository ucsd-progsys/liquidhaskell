module Strata where

import Prelude hiding (repeat, length)

{-@ LIQUID "--strata" @-}

data L a = N | Cons a (L a)
{-@ data L [llen] a = N | Cons (x::a) (xs::(L a)) @-}

{-@ measure llen :: L a -> Int
    llen (N) = 0
    llen (Cons x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v:L a | (llen v) >= 0} @-}

{-@ Cons :: forall <l>.a -> L^l a -> L^l a @-}


{-@ Lazy repeat @-}
repeat x = Cons x (repeat x)


-- length :: L a -> Int
length N = 0
length (Cons _ xs) = length xs

foo x = length (repeat x)

bar = repeat 
