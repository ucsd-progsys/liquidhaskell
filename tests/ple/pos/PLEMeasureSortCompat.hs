-- | Test that PLE does not apply a measure defined on [Int] to a [[Int]]
-- expression just because both share the [] type constructor.
-- This is a regression test for a bug where PLE's evalApp and
-- noUserDataMeasureEqs would apply all measures keyed by a data constructor
-- (e.g., (:)) to any constructor application, regardless of sort compatibility,
-- causing an elaboration crash: "Cannot unify int with [int]".

{-@ LIQUID "--ple" @-}

module PLEMeasureSortCompat where

{-@ reflect ms @-}
{-@ ms :: [[Int]] -> Nat @-}
ms :: [[Int]] -> Int
ms [] = 0
ms (x:xs) = 1 + m x + ms xs

{-@ measure m @-}
{-@ m :: xs:[Int] -> {v:Nat | len xs = v} @-}
m :: [Int] -> Int
m [] = 0
m (_:xs) = 1 + m xs

{-@ f :: xs:[[Int]] -> Int / [ms xs] @-}
f :: [[Int]] -> Int
f [] = 0
f (x:xs) =
  case drop 1 x of
    [] -> const (1 + f xs) lem1
    y  -> const (1 + f (y : xs)) lem2
      where
        lem2 = ms (y : xs)
 where
   lem1 = ms xs
