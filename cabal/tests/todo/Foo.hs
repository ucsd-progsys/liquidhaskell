module Geometry where  

import LiquidPrelude

myId x = x

myP :: Float -> Float
myP x = 3

abs0   :: Int -> Int 
abs0 x = if x > 0 then x else (-x)

abs1   :: Int -> Int 
abs1 x | x > 0     = x 
       | otherwise = -x

abs2 x = if x > 0 then x else (-x)

abs3 x | x > 0     = x 
       | otherwise = -x

pp :: Int -> Int -> Int
pp x y = x + y

fac :: Int -> Int 
fac n = plus n 1
