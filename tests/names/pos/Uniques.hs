-- TAG: local
-- tests local-var annotations; complicated by GHC adding TWO `go` binders (nested),
-- where picking the WRONG one to attach to the annotation yields an LH-GHC-mismatch.
-- [NOTE:] `Resolve.makeLocalVars` 

module Uniques (uniques) where

import qualified Data.Set as S 

-----------------------------------------------------------------------------------
-- | Code 
-----------------------------------------------------------------------------------
{-@ uniques :: (Eq a) => xs:_ -> {v:ListE a xs | noDups v} @-}
uniques :: (Eq a) => [a] -> [a]
uniques xs = go xs []
  where
    {-@ go :: (Eq a) => xs:_ -> acc:_ -> {v:ListU a acc xs | _ } @-}
    go (x:xs) acc 
          | x `isIn` acc = go xs acc     
          | otherwise    = go xs (x:acc)
    go [] acc        = acc 

{-@ isIn:: (Eq a) => x:a -> ys:[a] -> {v:Bool | v = S.member x (listElts ys)} @-}
isIn:: (Eq a) => a -> [a] -> Bool
isIn _ []     = False 
isIn x (y:ys) = x == y || isIn x ys

-----------------------------------------------------------------------------------
-- | Specification 
-----------------------------------------------------------------------------------
{-@ measure noDups @-}
noDups :: (Ord a) => [a] -> Bool
noDups []     = True 
noDups (x:xs) = noDups xs && not (S.member x (S.fromList xs)) 

{-@ type ListE a X   = {v:[a] | listElts v = listElts X} @-}
{-@ type ListU a X Y = {v:[a] | listElts v = S.union (listElts X) (listElts Y)} @-}
