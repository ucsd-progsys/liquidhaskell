{-@ LIQUID "--typed-holes" @-}

module ListToBST where

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
toBST = _goal
-- toBST xs = 
--     case xs of
--         [] -> Empty
--         x:xs' -> insert x (toBST xs')
