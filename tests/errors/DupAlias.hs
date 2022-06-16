{-@ LIQUID "--expect-error-containing=Multiple definitions of Type Alias `BoundedNat`" @-}
{-@ LIQUID "--expect-error-containing=Multiple definitions of Pred Alias `Foo`" @-}
module DupAlias () where

import Language.Haskell.Liquid.Prelude

{-@ type BoundedNat N = {v:Nat | v < N } @-}
{-@ predicate Foo V N = V < N            @-}

-- TODO: Test fails when this second alias is ALSO defined.
-- FIX: should WARN that there are duplicate aliases!

{-@ type BoundedNat N = {v:Nat | v <= N } @-}
{-@ predicate Foo V N = V <= N            @-}


{-@ foo :: n:Int -> m:(BoundedNat n) -> Nat @-}
foo :: Int -> Int -> Int
foo n m = liquidAssert (m < n) m
