{-# LANGUAGE FlexibleInstances #-}

module Instances where

class OptEq a where
  (==.) :: a -> a -> a

instance OptEq a where
{-@ instance OptEq a where
  ==. :: x:a -> y:{a| x == y} -> a
  @-}
  (==.) x _ = x



class OptEq2 a where
  cmp :: a -> a -> a

instance OptEq2 a where
{-@ instance OptEq2 a where
  cmp :: x:a -> y:{a| x == y} -> a
  @-}
  cmp x _ = x


-- This is unsoundly UNSAFE 

{- unsound :: x:Int -> {v:Int | v = x} -> Int @-}
unsound :: Int -> Int -> Int
unsound x y = x ==. y 

{-@ ok :: x:Int -> {v:Int | v = x} -> Int @-}
ok :: Int -> Int -> Int
ok x y = x `cmp` y 
