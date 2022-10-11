{-# LANGUAGE FlexibleInstances #-}

module T1126a where

class OptEq a where
  zoo :: a -> a -> a

instance OptEq a where
  {-@ instance OptEq a where
	zoo :: x:a -> y:{a | x == y} -> a
    @-}
  zoo x _ = x

instance OptEq Int where
  {-@ instance OptEq Int where
	zoo :: x:Int -> y:{Int| x == y} -> Int
    @-}
  zoo x _ = x

