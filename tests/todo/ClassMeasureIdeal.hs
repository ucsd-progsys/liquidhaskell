module Blank where

class Bob a where
  {-@ measure spl @-}
  spl :: a -> Int

  {-@ bob :: x:a -> {v:Int | v = 1 + spl x}
  bob :: a -> Int

data T1 = T1

instance Bob T1 where
  spl T1 = 1
  bob _  = 2

{-@ test1 :: T1 -> {v:Int | v = 2} @-}
test1 :: T1 -> Int
test1 T1 = bob T1
