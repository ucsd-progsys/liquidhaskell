-- LH issue #1023

{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--higherorder" @-}

module Bug (foo, zogbert) where

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect identity @-}
identity :: a -> a
identity x = x

{-@ reflect identity2 @-}
identity2 :: a -> a
identity2 x = x

{-@ reflect identity3 @-}
identity3 :: a -> a
identity3 x = x

{-@ foo :: x:a -> { identity x == x } @-}
foo :: a -> Proof
foo x = identity x ==. x *** QED

{-@ reflect zogbert @-}
zogbert :: a -> a
zogbert x = x
