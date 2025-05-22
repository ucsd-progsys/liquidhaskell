{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--save" @-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module T2535 where 

{- embed T as int @-}

{-@ f :: {v:AB (T a)  | check v} -> {v:AB (T a)  | check v} @-}
f ::  AB (T a) -> AB (T a) 
f x = g x 


data T a = T a  
data AB a  = A Int | B Int
{- data AB a = A Int | B Int @-}

{-@ measure check @-}
check :: AB ps -> Bool
check (A _) = True
check (B _) = False 

{-@ reflect g @-}
{-@ g :: {v:AB a | check v} -> {v:AB  a | check v} @-}
g ::  AB a -> AB a
g (A x) = A x 
g (B x) = B x  