module Fractional where

data Frac a

{-@ test :: x:Frac a -> y:{Frac a | y /= 0} -> {v:Frac a | v = x / y } @-} 
test :: Frac a -> Frac a -> Frac a 
test x y = x / y 


{-@ test1 :: x:a -> y:{a | y /= 0} -> {v:a | v = x / y } @-} 
test1 :: Fractional a => a -> a -> a  
test1 x y = x / y 

instance Num (Frac a) where
instance Fractional (Frac a) where
