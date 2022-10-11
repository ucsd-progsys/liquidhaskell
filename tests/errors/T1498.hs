{-@ LIQUID "--expect-error-containing=Standalone class method refinement" @-}
module T1498 where

class A a where
  f :: a -> Int

instance A Int where
  {-@ f :: _ -> {x : Int | 0 < x} @-}
  f n = n

{-@ x :: {x : Int | 0 < x} @-}
x :: Int
x = f ((-1) :: Int)
