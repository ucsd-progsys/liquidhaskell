module HOM where

{-@ LIQUID "--real" @-}
-- if forall types are not guarded 
-- (by type variables) then they get 
-- intstantiated as soon as enter the initial environment 

data BinOp a = Plus | Times

{-@ measure binOpDenote @-}
binOpDenote :: Int -> Int ->  BinOp a -> Int
binOpDenote x y Plus  = (x + y)
binOpDenote x y Times = (x * y)


plus = Plus 
times = Times 