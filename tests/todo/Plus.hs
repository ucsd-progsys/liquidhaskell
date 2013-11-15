module Plus where

go :: Int -> Int -> Int -> Int
{-@ go :: x:Int -> y:Int -> {v:Int|v = x-y+1} -> Int @-}
go _ _ _ = undefined


go' :: Int -> Int -> Int -> Int
{-@ go' :: x:Int -> y:Int -> {v:Int|v = (x-y)+1} -> Int @-}
go' _ _ _ = undefined


bar x y z 
  = if z then go x y (x-y+1) 
         else go' x y (x-y+1)
