{-@ LIQUID "--typed-holes" @-}

module ListQuickSort where

import qualified Data.Set as S
import           Language.Haskell.Liquid.Synthesize.Error

{-@ data IList [iLen] a =  
      N
    | ICons { x :: a, xs :: IList { v: a | x <= v } }
  @-}
data IList a = N | ICons a (IList a)

{-@ measure iLen @-}
{-@ iLen :: IList a -> Nat @-}
iLen :: IList a -> Int
iLen N            = 0
iLen (ICons x xs) = 1 + iLen xs

{-@ measure iElts @-}
{-@ iElts :: IList a -> S.Set a @-}
iElts :: Ord a => IList a -> S.Set a
iElts N            = S.empty
iElts (ICons x xs) = S.union (S.singleton x) (iElts xs)

{-@ partition :: p: a -> xs: [a]
        -> { v: ([ { v: a | v <= p} ], [ { v: a | v > p } ]) |  len (fst v) + len (snd v) == len xs && 
                                                                S.union (listElts (fst v)) (listElts (snd v)) == listElts xs } 
  @-}
partition :: Ord a => a -> [a] -> ([a], [a])
partition p xs = 
    case xs of
        [ ]   -> ([ ], [ ])
        x5:x6 -> case partition p x6 of
                    (x11, x12) -> if x5 <= p then (x5:x11, x12)
                                             else (x11, x5:x12)

{-@ pivotAppend :: p: a -> xs: IList { v: a | v <= p } -> ys: IList { v: a | v > p } 
        -> { v: IList a | iLen v == iLen xs + iLen ys + 1 && 
                          iElts v == S.union (S.union (iElts xs) (iElts ys)) (S.singleton p) } 
  @-}
pivotAppend :: Ord a => a -> IList a -> IList a -> IList a
pivotAppend p xs ys =
    case xs of  N           -> ICons p ys
                ICons x5 x6 -> ICons x5 (pivotAppend p x6 ys)

{-@ quickSort :: xs: [a] -> { v: IList a | iLen v == len xs && iElts v == listElts xs } @-}
quickSort :: Ord a => [a] -> IList a
quickSort = _goal
-- quickSort xs =
--   case xs of
--     [ ]   -> N
--     x3:x4 -> case partition x3 x4 of (x9, x10) -> pivotAppend x3 (quickSort x9) (quickSort x10)
