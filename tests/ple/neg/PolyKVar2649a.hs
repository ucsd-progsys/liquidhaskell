{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple" @-}
-- | Simple variant of issue #2649: calling a helper with open kvar refinements
-- from a function that requires a concrete postcondition involving Data.Set.
-- Previously crashed with a sort mismatch in elaboration.
module PolyKVar2649a where

import qualified Data.Set as S

{-@ go :: {acc:[a] | _} -> {v:[a] | _ } @-}
go :: [a] -> [a]
go xs = xs

{-@ uniques :: (Eq a) => xs:[a] -> {v:ListE a xs | noDups v} @-}
uniques :: (Eq a) => [a] -> [a]
uniques xs = go xs

{-@ reflect noDups @-}
noDups :: (Ord a) => [a] -> Bool
noDups []     = True
noDups (x:xs) = noDups xs && not (S.member x (S.fromList xs))

{-@ type ListE a X = {v:[a] | S.listElts v = S.listElts X} @-}
