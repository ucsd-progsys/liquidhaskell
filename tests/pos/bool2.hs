module EqBool where 


{-@ gerb :: (Ord a) => x:a -> {v:a | x <= v } -> {v:a | x <= v} @-}
gerb :: (Ord a) => a -> a -> a 
gerb x y = y 

 
moo = gerb False False 
