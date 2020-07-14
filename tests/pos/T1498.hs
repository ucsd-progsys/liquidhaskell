module T1498 where

class FromTo a where 
  from :: a -> Int 
  to   :: Int -> a 

{-@ instance FromTo Int where
      from :: Int -> {v:Int | 0 <= v };
      to   :: {v:Int | 0 <= v } -> Int
@-}

instance FromTo Int where 
  from x = if 0 <= x then x else -x  
  to   x = x 
