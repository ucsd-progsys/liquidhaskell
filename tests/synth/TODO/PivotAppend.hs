{-@ LIQUID "--typed-holes" @-}

module PivotAppend where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ data IList [iLen] a = N | ICons { x0 :: a, xs0 :: IList { v: a | x0 <= v } } @-}
data IList a = N | ICons a (IList a)

{-@ measure iLen @-}
{-@ iLen :: IList a -> Nat @-}
iLen :: IList a -> Int
iLen N            = 0
iLen (ICons x xs) = 1 + iLen xs

{-@ measure iElts @-}
{-@ iElts :: IList a -> S.Set a @-}
iElts N            = S.empty
iElts (ICons x xs) = S.union (S.singleton x) (iElts xs)

{-@ pivotAppend :: p: a -> xs: IList { v: a | v <= p } -> ys: IList { v: a | v > p } 
        -> { v: IList a | iLen v == iLen xs + iLen ys + 1 && 
                          iElts v == S.union (S.union (iElts xs) (iElts ys)) (S.singleton p) } 
  @-}
pivotAppend :: a -> IList a -> IList a -> IList a
pivotAppend = _goal
-- pivotAppend p xs ys =
--       case xs of
--         N -> ICons p ys
--         ICons x5 x6 -> ICons x5 (pivotAppend p x6 ys)
