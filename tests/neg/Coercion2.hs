{-@ LIQUID "--expect-error-containing=len ?a" @-}
{-@ LIQUID "--expect-error-containing=: GHC.Internal.Types.Int | false" @-}

-- | Tests that pattern matching on newtypes does not
-- disable subtyping checks.
module Coercion2 where

newtype Index = Index Int

{-@ toIx :: xs:[Int] -> Index -> {v:Nat | v < len xs} @-}
toIx :: [Int] -> Index -> Int
toIx _ (Index i) = i

{-@ pick :: [Int] -> Index -> Int @-}
pick :: [Int] -> Index -> Int
pick xs i = xs !! toIx xs i

{-@ unwrapFalse :: Index -> {v:Int | false} @-}
unwrapFalse :: Index -> Int
unwrapFalse (Index i) = i

main :: IO ()
main = print (pick [1, 2, 3] (Index 5))
