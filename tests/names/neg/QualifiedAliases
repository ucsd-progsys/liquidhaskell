{-@ LIQUID "--expect-error-containing=Multiple definitions of Type Alias" @-}

-- | This is an instance of LiquidHaskell having a flat import namespace
-- for logic names. Here, both Nat modules export the same type alias 'INat',
-- producing an error even though we explicitly qualify it to avoid ambiguity.
module QualifiedAliases where

import qualified Nat1 as N
import Nat2

{-@ llength :: [a] -> Nat @-}
llength :: [a] -> Int
llength [] = 0
llength (x : xs) = 1 + length xs
