
-- https://github.com/ucsd-progsys/liquidhaskell/issues/870 
-- the following succeeds normally, but fails if we switch on the higher-order 

{- LIQUID "--higherorder" @-}

import Prelude hiding (splitAt)


data Vec a = Nil | Cons a (Vec a)

{-@ invariant {v:Vec a | 0 <= vlen v} @-}

{-@ measure vlen :: Vec a -> Int
    vlen Nil         = 0
    vlen (Cons x xs) = 1 + vlen xs
  @-}


{-@ splitAt :: n:Nat
            -> a:{Vec t|vlen a >= n}
            -> {b:(Vec t, Vec t)|vlen (snd b) = vlen a - n && n = vlen (fst b)} @-}

splitAt :: Int -> Vec a -> (Vec a, Vec a)
splitAt 0         as  = (Nil, as)
splitAt n (Cons a as) = let (b1, b2) = splitAt (n - 1) as
                        in (Cons a b1, b2)

