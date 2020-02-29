{-@ LIQUID "--typed-holes" @-}

module TreeCount where

import Language.Haskell.Liquid.Synthesize.Error

{-@ data Tree [size] a = 
              Empty 
            | Node { x :: a, l :: Tree a, r :: Tree a } 
  @-}
data Tree a = Empty | Node a (Tree a) (Tree a)

{-@ measure size @-} 
{-@ size :: Tree a -> Nat @-}
size :: Tree a -> Int
size Empty        = 0
size (Node x l r) = size l + size r + 1
  
{-@ zero :: { v: Int | v == 0 } @-}
zero :: Int 
zero = 0

{-@ one :: { v: Int | v == 1 } @-}
one :: Int
one = 1

{-@ plus :: x: Int -> y: Int -> { v: Int | v == x + y} @-}
plus :: Int -> Int -> Int
plus x y = x + y
	
{-@ countNodes :: t: Tree a -> { v: Int | v == size t } @-}
countNodes :: Tree a -> Int
countNodes = _goal
-- countNodes t =
--     case t of
--         Empty -> zero
--         Node x4 x5 x6 -> plus one (plus (countNodes x5) (countNodes x6))

