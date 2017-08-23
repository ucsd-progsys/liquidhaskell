module LiquidArray where

{-@ set :: forall a <p :: x0: Int -> x1: a -> Bool, r :: x0: Int -> Bool>.
      i: Int<r> ->
      x: a<p i> ->
      a: (j: {v: Int<r> | v != i} -> a<p j>) ->
      (k: Int<r> -> a<p k>) @-}
set :: Int -> a -> (Int -> a) -> (Int -> a)
set i x a = \k -> if k == i then x else a k

{-@ get :: forall a <p :: x0: Int -> x1: a -> Bool, r :: x0: Int -> Bool>.
             i: Int<r> ->
             a: (j: Int<r> -> a<p j>) ->
             a<p i> @-}
get :: Int -> (Int -> a) -> a
get i a = a i

{-@ empty :: i: {v: Int | 0 = 1} -> a @-}
empty :: Int -> a
empty = const undefined 
