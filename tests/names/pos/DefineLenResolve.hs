-- | Regression test: user-written `define length x = len x` must resolve
-- the bare `len` symbol to the qualified class measure, so reflected
-- functions that use `length` in their body (and metric) pass sort-checking.
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module DefineLenResolve where

{-@ reflect ms @-}
{-@ ms :: [[Int]] -> Nat @-}
ms :: [[Int]] -> Int
ms [] = 0
ms (x:xs) = 1 + length x + ms xs

{-@
define length x = len x
@-}

{-@ f :: xs:[[Int]] -> Int / [ms xs] @-}
f :: [[Int]] -> Int
f [] = 0
f (x:xs) = 1 + f xs
