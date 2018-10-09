-- Tests that we DON'T generalize type aliases before normalizing

module LibAliasGen00 where

{-@ type Floo a N = {v:[a] | len v = N} @-}

{-@ assume foo :: n:Nat -> Floo Int n @-}
foo :: Int -> [Int]
foo _ = undefined

