{-@ LIQUID "--typed-holes" @-}

module ListInsertSort where

import qualified Data.Set as S

import Language.Haskell.Liquid.Synthesize.Error

{-@ data IList a = N | C { x :: a, xs :: (IList { v: a | x <= v}) } @-}
data IList a = N | C a (IList a)

{-@ measure iLen @-}
{-@ iLen :: IList a -> Nat @-}
iLen :: IList a -> Int
iLen N        = 0
iLen (C x xs) = 1 + iLen xs

{-@ measure iElems @-}
{-@ iElems :: IList a -> S.Set a @-}
iElems :: Ord a => IList a -> S.Set a
iElems N = S.empty 
iElems (C x xs) = S.union (S.singleton x) (iElems xs)
 	
{-@ insert :: x: a -> xs: IList a -> { v: IList a | iElems v == S.union (S.singleton x) (iElems xs) } 
  @-}
insert :: Ord a => a -> IList a -> IList a
insert x N  
    = C x N
insert x (C x0 xs) 
    = if x <= x0 then C x (C x0 xs) else C x0 (insert x xs)

{-@ insertSort :: xs: [a] -> { v: IList a | iElems v == listElts xs } @-}
insertSort x_S1 =
    case x_S1 of
        [] -> N
        (:) x_Sc x_Sd -> insert x_Sc (insertSort x_Sd)
