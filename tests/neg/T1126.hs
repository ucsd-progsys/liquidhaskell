{-@ LIQUID "--expect-any-error" @-}
{-# LANGUAGE FlexibleInstances #-}

module T1126 where

class OptEq a where
  (==.) :: a -> a -> a

instance OptEq a where
  (==.) x _ = x

{-@ instance OptEq a where 
      ==. :: x:a -> y:{a| x == y} -> a
  @-}


class OptEq2 a where
  cmp :: a -> a -> a

instance OptEq2 a where
  cmp x _ = x

{-@ instance OptEq2 a where 
      cmp :: x:a -> y:{a| x == y} -> a
  @-}

-- This is unsoundly UNSAFE 

{- unsound :: x:Int -> {v:Int | v = x} -> Int @-}
unsound :: Int -> Int -> Int
unsound x y = x ==. y 

{-@ ok :: x:Int -> {v:Int | v = x} -> Int @-}
ok :: Int -> Int -> Int
ok x y = x `cmp` y 
