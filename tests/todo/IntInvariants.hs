module Invariant where


{-@ invariant {v : Int | v > 0 } @-}


-- This is unsoundly safe

{-@ bar :: Nat @-}
bar :: Int
bar = let x = -5 in x

-- but this is not
--
{-@ foo :: Nat @-}
foo :: Int
foo = -5

