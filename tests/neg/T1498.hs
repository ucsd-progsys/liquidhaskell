{-@ LIQUID "--expect-any-error" @-}
module T1498 where

class FromTo a where 
  from :: a -> Int 
  to   :: Int -> a 

{-@ instance FromTo Int where 
      from :: Int -> {v:Int | 0 <= v };
      to   :: {v:Int | 0 <= v } -> Int 
@-}

instance FromTo Int where 
  from x = x -- if 0 <= x then x else -x  
  to   x = x 


class A a where
  f :: a -> Int

{-@ instance A Int where
      f :: Int -> {x : Int | 0 < x}
  @-}
instance A Int where
  f n = (-1)

{-@ g :: Int -> {n : Int | 0 < n} @-}
g :: Int -> Int
g x = f x
