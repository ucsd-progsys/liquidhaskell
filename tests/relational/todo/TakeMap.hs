module Fixme where

mapTake :: Int -> (a -> a) -> [a] -> [a]
mapTake n g l = map g (take n l)

takeMap :: Int -> (a -> a) -> [a] -> [a]
takeMap n g l = take n (map g l)

{-@ relational takeMap ~ mapTake 
      :: n1:Int -> g1:(a -> a) -> l1:[a] -> [a] ~ n2:Int -> g2:(a -> a) -> l2:[a] -> [a]
      ~~ r1 n1 g1 l1 == r2 n2 g2 l2 @-}