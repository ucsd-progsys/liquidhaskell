{-@ LIQUID "--typed-holes" @-}

module BSTFlatten where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ data BST [size] a = 
      Empty 
    | Node { x :: a, l :: BST { v: a | v < x }, r :: BST { v: a | x < v } } 
  @-}
data BST a = Empty | Node a (BST a) (BST a)

{-@ measure size @-}
{-@ size :: BST a -> Nat @-}
size :: BST a -> Int
size Empty        = 0
size (Node x l r) = 1 + size l + size r

{-@ measure bstElts @-}
{-@ bstElts :: BST a -> S.Set a @-}
bstElts :: Ord a => BST a -> S.Set a 
bstElts Empty = S.empty
bstElts (Node x l r) = S.union (S.singleton x) (S.union (bstElts l) (bstElts r))

{-@ insert :: x: a -> t: BST a -> { v: BST a | bstElts v == S.union (S.singleton x) (bstElts t) } @-}
insert :: Ord a => a -> BST a -> BST a
insert x t = 
    case t of 
        Empty -> Node x Empty Empty
        Node y l r -> 
            if x == y
                then t
                else if y <= x 
                        then Node y l (insert x r)
                        else Node y (insert x l) r

{-@ toBST :: xs: [a] -> { v: BST a | listElts xs == bstElts v } @-}
toBST :: Ord a => [a] -> BST a
toBST xs = 
    case xs of
        [] -> Empty
        x:xs' -> insert x (toBST xs')

{-@ data IList [iLen] a = N | ICons { x0 :: a, xs0 :: IList { v: a | x0 < v } } @-}
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

{-@ pivotAppend :: p: a -> xs: IList { v: a | v < p } -> ys: IList { v: a | v > p } 
        -> { v: IList a | iLen v == iLen xs + iLen ys + 1 && 
                          iElts v == S.union (S.union (iElts xs) (iElts ys)) (S.singleton p) } 
  @-}
pivotAppend :: a -> IList a -> IList a -> IList a
pivotAppend p xs ys =
      case xs of
        N -> ICons p ys
        ICons x5 x6 -> ICons x5 (pivotAppend p x6 ys)

{-@ flatten :: t: BST a -> { v: IList a | iElts v == bstElts t } @-}
flatten :: BST a -> IList a 
flatten = _goal
