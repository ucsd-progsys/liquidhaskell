{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple" @-}
-- | Original example from issue #2649: polymorphic kvar type variable mismatch
-- when a local helper function 'go' uses a different type variable than the
-- outer function 'uniques'. Previously crashed with a sort mismatch in elaboration.
module PolyKVar2649b (uniques) where

import qualified Data.Set as S

{-@ uniques :: (Eq a) => xs:_ -> {v:ListE a xs | noDups v} @-}
uniques :: (Eq a) => [a] -> [a]
uniques xs = go xs []
  where
    {-@ go :: (Eq a) => xs:_ -> acc:_ -> {v:ListU a acc xs | _ } @-}
    go (x:xs) acc
          | x `isIn` acc = go xs acc
          | otherwise    = go xs (x:acc)
    go [] acc        = acc

{-@ isIn :: (Eq a) => x:a -> ys:[a] -> {v:Bool | v = S.member x (S.listElts ys)} @-}
isIn :: (Eq a) => a -> [a] -> Bool
isIn _ []     = False
isIn x (y:ys) = x == y || isIn x ys

{-@ reflect noDups @-}
noDups :: (Ord a) => [a] -> Bool
noDups []     = True
noDups (x:xs) = noDups xs && not (S.member x (S.fromList xs))

{-@ type ListE a X   = {v:[a] | S.listElts v = S.listElts X} @-}
{-@ type ListU a X Y = {v:[a] | S.listElts v = S.union (S.listElts X) (S.listElts Y)} @-}
