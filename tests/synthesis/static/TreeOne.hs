{-@ LIQUID "--typed-holes" @-}

module TreeOne where

import Language.Haskell.Liquid.Synthesize.Error

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
one x_S0 = Node x_S0 Empty Empty