-- | Disambiguate between type aliases with the same name
-- coming from distinct imports using the name qualified.
--
-- Here, both @Nat@ modules export a type alias with
-- the same name @INat@. The appropiate alias is used in each case.
-- This example shows that we can use both the unqualified or qualified name
-- when the import is not qualified.
-- If a module is imported qualified (with an alias)
-- we need to use the type alias qualified as well (with the module alias).
--
-- The resulting spec stores/exports the type alias coming from the last module
-- according to lexicographic order. So here, @INat@ from 'Nat2' is exported by
-- this module.
-- See @test/names/pos/ImportedTypeAlias.hs@
module QualifiedTypeAliases where

import Data.Int (Int32)
import qualified Nat1 as N
import Nat2

{-@ llength :: [a] -> INat @-}
llength :: [a] -> Int32
llength [] = 0
llength (x : xs) = 1 + llength xs

{-@ llength' :: [a] -> N.INat @-}
llength' :: [a] -> Int
llength' [] = 0
llength' (x : xs) = 1 + llength' xs

{-@ test :: Nat2.INat@-}
test :: Int32
test = 0

{-@ testFoo :: NatFoo@-}
testFoo :: Int
testFoo = 1
