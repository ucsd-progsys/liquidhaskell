{-@ LIQUID "--ple" @-}

module Blank where

class Bob a where
  {-@ reflect spl @-}
  spl :: a -> a -> Int

  {-@ bob :: x:a -> {v:Int | v = (spl x x)}
  bob :: a -> Int

data T1 = T1

instance Bob T1 where
  spl T1 T1 = 1
  bob _     = 1

{-@ test1 :: T1 -> {v:Int | v = 1} @-}
test1 :: T1 -> Int
test1 T1 = bob T1
