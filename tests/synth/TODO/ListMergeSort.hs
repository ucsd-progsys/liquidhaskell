{-@ LIQUID "--typed-holes" @-}

module ListMergeSort where

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

{-@ inline abs' @-}
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' x = if x >= 0 then x else -x

{-@ split :: xs: [a] 
        -> { v: ({ v: [a] | abs' (len xs - len v * 2) <= 1}, [a]) | len (fst v) + len (snd v) == len xs && 
                                                                    S.union (listElts (fst v)) (listElts (snd v)) == listElts xs } 
  @-}
split :: [a] -> ([a], [a])
split xs = 
    case xs of 
        [] -> (xs, xs)
        x5:x6 -> 
            case x6 of
                [] -> (x6, xs)
                x11:x12 ->
                    case split x12 of
                        (x16, x17) -> (x11:x16, x5:x17)

--  { ys: IList a | abs' (iLen ys - iLen xs) <= 1 } 
{-@ merge :: xs: IList a -> ys: IList a
        -> { v: IList a | iLen v == iLen xs + iLen ys && iElts v == S.union (iElts xs) (iElts ys) } 
        / [ iLen xs + iLen ys ] 
  @-}
merge :: Ord a => IList a -> IList a -> IList a
merge N            N            = N
merge xs           N            = xs
merge N            xs           = xs
merge (ICons x xs) (ICons y ys) = 
    if x <= y 
        then ICons x (merge xs (ICons y ys)) 
        else ICons y (merge (ICons x xs) ys)

{-@ mergeSort :: xs: [a] -> { v: IList a | iLen v == len xs && iElts v == listElts xs } @-}
mergeSort :: Ord a => [a] -> IList a
mergeSort = _goal
-- mergeSort xs =
--   case xs of
--     [ ]   -> N
--     x3:x4 -> 
--       case x4 of
--         [ ]    -> ICons x3 N
--         x9:x10 -> case split xs of 
--                     (x14, x15) -> merge (mergeSort x14) (mergeSort x15)

