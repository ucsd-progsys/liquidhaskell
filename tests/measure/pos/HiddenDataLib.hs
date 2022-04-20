module HiddenDataLib where

{-@ data Thing = Red Nat | Blue Nat @-}
data Thing = Red Int | Blue Int 

{-@ blub :: Nat -> Nat @-}
blub :: Int -> Int 
blub x = x + 1
