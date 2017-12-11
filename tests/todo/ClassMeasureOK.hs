module Blank where

{-@ class measure spl :: forall a. a -> Int @-}

class Bob a where
  {-@ class Bob a where
	  spl :: x:a -> {v:Int | v = spl x}
	  bob :: a -> Int
    @-}
  spl :: a -> Int
  bob :: a -> Int

data T1 = T1

instance Bob T1 where
  {-@ instance measure spl :: T1 -> Int
        spl T1 = 1
    @-}
  spl T1 = 1
  bob _  = 1

{-@ test1 :: T1 -> {v:Int|v = 1} @-}
test1 :: T1 -> Int
test1 T1 = spl T1
