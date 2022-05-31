{-@ LIQUID "--expect-any-error" @-}
module T1498A where

class FromTo a where 
  from :: a -> Int 
  to   :: Int -> a 


{-@ class FromTo a where 
      from :: a -> {v:Int | 10 <= v } 
      to   :: Int -> a  
  @-}
  

{-@ instance FromTo Int where 
      from :: Int -> {v:Int | 0 <= v };
      to   :: x:{Int | 0 <= x } -> {v:Int | v ==  x} 
  @-}

instance FromTo Int where 
  from x = if 0 <= x then x else -x  
  to   x = x 

bar :: Int -> Int 
bar x = bar x 
