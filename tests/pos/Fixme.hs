{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
module Optional where

class OptEq a r where
  (==!) :: a -> a -> r 

instance OptEq a (Bool -> a) where
{-@ instance OptEq a (Bool -> a) where 
  ==! :: x:a -> y:{a | x == y} -> Bool -> {v:a | v == x }
  @-}
  (==!) x _ _ = x 

instance OptEq a a where
{-@ instance OptEq a a where 
  ==! :: x:a -> y:{a| x == y} -> {v:a | v == x }
  @-}
  (==!) x y = (==!) x y True  


{-@ _5 :: {v:Int | v == 5} @-}
_5 :: Int
_5 = 5 

{- bar :: x:Int -> y:{Int | x == y} -> {v:Int | v == x} @-} 
bar :: Int 
bar = (==!) exp1 exp2
  where
    exp1 :: Int 
    exp2 :: Int 
    exp1 = 5 
    exp2 = 5   

{-@ foo :: (OptEq a a) => x:a -> y:a -> {v:Bool | x == y} -> {v:a | v == x} @-} 
foo :: (OptEq a a) => a -> a -> Bool -> a 
foo  = (==!)  
