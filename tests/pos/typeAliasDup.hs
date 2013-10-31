module Goo where

import Language.Haskell.Liquid.Prelude

{-@ type BoundedNat N = {v:Nat | v < N } @-}

-- TODO: Test fails when this second alias is ALSO defined.
-- FIX: should WARN that there are duplicate aliases!

{-@ type BoundedNat N = {v:Nat | v <= N } @-}


{-@ foo :: n:Int -> m:(BoundedNat n) -> Nat @-}
foo :: Int -> Int -> Int
foo n m = liquidAssert (m < n) m
