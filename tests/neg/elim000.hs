module Poslist () where

{-@ prop2 :: Int -> Nat @-}
prop2 :: Int -> Int
prop2 x = numAbsList x

numAbsList = glap numAbs

{-@ glap :: (a -> b) -> a -> b @-}
glap :: (a -> b) -> a -> b
glap = undefined

-- Adding the below signature makes it flag an error...
-- numAbs :: Int -> Int
numAbs x = if x > 0 then x else x
