-- TODO-REBARE: this _should_ be unsafe (apparently) but thats not happening...

{-@ LIQUID "--strata" @-}

module Strata where

import Prelude hiding (repeat, length)

data L a = N | Cons a (L a)
{-@ data L [llen] @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen (N) = 0
llen (Cons x xs) = 1 + (llen xs)

{-@ Cons :: forall <l>.a -> L^l a -> L^l a @-}

{-@ lazy repeat @-}
repeat x = Cons x (repeat x)

-- length :: L a -> Int
length N           = 0
length (Cons _ xs) = length xs

foo x = length (repeat x)

bar = repeat 
