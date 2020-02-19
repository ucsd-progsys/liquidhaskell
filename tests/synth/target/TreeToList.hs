{-@ LIQUID "--typed-holes" @-}

module TreeToList where

import qualified Data.Set as S

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined


{-@ data Tree [size] a = 
      Empty 
    | Node { x:: a, l:: (Tree a), r:: (Tree a) } 
  @-}
data Tree a = Empty | Node a (Tree a) (Tree a)

{-@ measure size @-}
{-@ size :: Tree a -> Nat @-}
size :: Tree a -> Int 
size Empty = 0
size (Node x l r) = 1 + size l + size r 

{-@ append' :: x: [a] -> y: [a] 
      -> { v: [a] | len v == len x + len y && 
                    S.union (listElts x) (listElts y) == listElts v }
  @-}
append' :: [a] -> [a] -> [a]
append' []     xs = xs
append' (y:ys) xs = y : append' ys xs

{-@ measure treeElts @-}
{-@ treeElts :: Tree a -> Set a @-}
treeElts Empty        = S.empty
treeElts (Node x l r) = S.union (S.singleton x) (S.union (treeElts l) (treeElts r))

{-@ toList :: x: Tree a 
      -> { v: [a] | len v == size x && listElts v == treeElts x} 
  @-}
toList :: Tree a -> [a]
toList = _goal
-- toList t = 
--     case t of
--         Empty -> []
--         Node x l r -> x : (append' (toList l) (toList r))
