{-@ LIQUID "--expect-any-error" @-}

-- | This is an instance of LiquidHaskell having a flat import namespace
-- for logic names. Here, both @Nat@ modules export a type alias with
-- the same name @INat@. With current behavior this module produces a
-- _Multiple definition of Type Alias_ error when using the alias unqualified,
-- and an _Unknown type constructor_ error with the qualified alias.
-- NOTE: This test will be moved to @names-pos@ after fixing issue #2841
module QualifiedAliases where

import qualified Nat1 as N
import Nat2

{-@ llength :: [a] -> INat @-}
llength [] = 0
llength (x : xs) = 1 + length xs

{-@ llength' :: [a] -> N.INat @-}
llength' [] = 0
llength' (x : xs) = 1 + length xs
