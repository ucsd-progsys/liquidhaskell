{-@ LIQUID "--typed-holes" @-}

module TreeOne where

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

{-@ one :: x: a -> {v: Tree a | size v == 1} @-}
one :: a -> Tree a 
one = _goal