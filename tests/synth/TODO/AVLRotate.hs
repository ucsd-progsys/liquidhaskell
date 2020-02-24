{-@ LIQUID "--typed-holes" @-}

module AVLRotate where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error 

{-@ inc :: x: Int -> { v: Int | v == x + 1} @-}
inc :: Int -> Int 
inc x = x + 1

{-@ data AVL [realHeight] a = 
    Leaf 
  | Node { 
        x :: a
      , l :: AVL { v: a | v < x}
      , r :: { v: AVL { v: a | v > x} | abs' (realHeight l - realHeight v) <= 1 }
      , h :: { v: Int | v == 1 + max' (realHeight l) (realHeight r) }
    } 
  @-}
data AVL a = Leaf | Node a (AVL a) (AVL a) Int

{-@ inline max' @-}
{-@ max' :: Int -> Int -> Int @-}
max' :: Int -> Int -> Int 
max' x y = if x >= y then x else y

{-@ inline abs' @-}
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int 
abs' x = if x >= 0 then x else -x 

{-@ measure realHeight @-}
{-@ realHeight :: AVL a -> Nat @-}
realHeight :: AVL a -> Int 
realHeight Leaf = 0
realHeight (Node x l r h) = 1 + max' (realHeight l) (realHeight r)

{-@ measure balFac @-}
{-@ balFac :: AVL a -> Int @-}
balFac :: AVL a -> Int
balFac Leaf = 0
balFac (Node x l r h) = realHeight l - realHeight r

{-@ measure avlElts @-}
{-@ avlElts :: AVL a -> S.Set a @-}
avlElts :: Ord a => AVL a -> S.Set a
avlElts Leaf = S.empty
avlElts (Node x l r h) = S.union (S.singleton x) (S.union (avlElts l) (avlElts r))

{-@ rotRR :: x: a 
          -> l: AVL { v: a | v < x}
          -> { r: AVL { v: a | v > x} | realHeight r - realHeight l == 2 && balFac r < 0 } 
          -> { v: AVL a | realHeight v == realHeight r && 
                          avlElts v == S.union (S.singleton x) (S.union (avlElts l) (avlElts r)) } 
  @-}
-- rotRR = _goal1
rotRR :: a -> AVL a -> AVL a -> AVL a
rotRR x l r =
      case r of
        Leaf -> error ""
        Node x5 x6 x7 x8 -> 
          case x7 of
            Leaf -> error ""
            Node x13 x14 x15 x16 -> Node x5 (Node x l x6 x16) x7 x8

{-@ rotRL :: x: a 
          -> l: AVL { v: a | v < x}
          -> { r: AVL { v: a | v > x} | realHeight r - realHeight l == 2 && balFac r > 0 } 
          -> { v: AVL a | realHeight v == realHeight r && avlElts v == S.union (S.singleton x) (S.union (avlElts l) (avlElts r)) } 
  @-}
-- rotRL = _goal2
rotRL :: a -> AVL a -> AVL a -> AVL a
rotRL x l r = 
  case r of
    Leaf -> error "error"
    Node x5 x6 x7 x8 -> 
          case x6 of
            Leaf -> error "error"
            Node x13 x14 x15 x16 -> Node x13 (Node x l x14 x16) (Node x5 x15 x7 x16) x8

{-@ rotR0 :: x: a 
          -> l: AVL { v: a | v < x}
          -> { r: AVL { v: a | v > x } | realHeight r - realHeight l == 2 && balFac r == 0 }
          -> { v: AVL a | realHeight v == 1 + realHeight r && avlElts v == S.union (S.singleton x) (S.union (avlElts l) (avlElts r)) } 
  @-}
rotR0 :: a -> AVL a -> AVL a -> AVL a
-- rotR0 = _goal3
rotR0 x l r =
  case r of
    Leaf -> error ""
    Node x5 x6 x7 x8 -> Node x5 (Node x l x6 x8) x7 (inc x8)
