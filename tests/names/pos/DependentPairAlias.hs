-- | Regression test for https://github.com/ucsd-progsys/liquidhaskell/issues/2590
-- Name resolution should work for dependent pairs with type aliases.
module DependentPairAlias where

{-@ type Ix ty R = { val:ty | val = R } @-}

{-@ foo :: (v::Int, { r:Int | r = v }) @-}
foo :: (Int, Int)
foo = (3, 3)

{-@ bar :: (v::Int, Ix Int v) @-}
bar :: (Int, Int)
bar = (3, 3)
