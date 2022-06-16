{-@ LIQUID "--expect-error-containing=Bad Data Specification" @-}
module T1498A where

class A a where
  f :: a -> Int
  
instance A Int where
{-@ instance A Int where
      f :: _ -> {x : Int | 0 < x}
  @-}
  f n = (-1)
