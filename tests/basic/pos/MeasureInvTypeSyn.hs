-- | Test that a measure defined on a type synonym (expanding to a list with
-- a structured element type) does not spuriously propagate its Nat invariant
-- to plain list binders with a type-variable element type.
-- This is a regression test for a bug where the invariant for 'ms' (which
-- expects [Diff [a]]) was incorrectly applied to [a] binders, causing an
-- elaboration failure: "Cannot unify a with (Diff [..])".

module MeasureInvTypeSyn where

{-@ LIQUID "--ple" @-}

data Diff a = First a | Second a | Both a a
type Hunk a = [Diff [a]]

{-@ measure ms @-}
{-@ ms :: Hunk a -> Nat @-}
ms :: Hunk a -> Int
ms [] = 0
ms (x:xs) = 1 + m x + ms xs

{-@ measure m @-}
{-@ m :: Diff [a] -> Nat @-}
m :: Diff [a] -> Int
m (First _) = 1
m (Second _) = 1
m (Both xs _) = length' xs

{-@ measure length' @-}
{-@ length' :: xs:[a] -> Nat @-}
length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs

{-@ f :: xs0:Hunk a -> Int / [ms xs0] @-}
f :: Hunk a -> Int
f [] = 0
f ((Both (_:x) y):xs) = 1 + f (Both x y:xs)
f (_:xs) = 1 + f xs
