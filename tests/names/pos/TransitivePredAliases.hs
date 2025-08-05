-- | Predicate aliases accumulate transitively, i.e. a module exports all the
-- predicate aliases from its transitive dependencies.
-- But, when two different predicate aliases share the same unqualified name
-- we take the following precedence to decide which to store in the lifted spec:
-- 1. The locally defined one.
-- 2. The last according to the lexicographic order of the module we imported it from.
--
-- We have the following dependency graph:
--
--        ExprAliases           ExprAliasesCopycat
--                 \             /
--                  \           /
--               QualifiedPredAliases
--                        |
--                        |
--               TransitivePredAliases
--
-- So all logic names from @ExprAliases@ actually come from @ExprAliasesCopycat@,
-- and the @LessThanSomeNum@ predicate (defined in all dependencies) comes
-- from @QualifiedPredAliases@.
module TransitivePredAliases where

import QualifiedPredAliases

{-@ nine :: { n : Integer | LessThanSomeNum n }@-}
nine :: Integer
nine = 9

{-@ twenty :: { n:Int | InSomeRange n }@-}
twenty :: Int
twenty = 20

{-@ oneDividesAll :: n:Int -> { _:() | Divides 1 n } @-}
oneDividesAll :: Int -> ()
oneDividesAll _ = ()

{-@ negTwo :: { v:Int | Negative v }@-}
negTwo :: Int
negTwo = -2

{-@ transThree :: p:(Int,Int) ->
               { p':(Int,Int) | DiffBound (fst p') (snd p') (fst p - snd p) } @-}
transThree :: (Int,Int) -> (Int,Int)
transThree (x,y) = (x + 3, y + 3)
