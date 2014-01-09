module Meas () where

import Data.Set (Set(..))

{-@ myid :: xs:[a] -> {v:[a]| listElts(v) = listElts(xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs

{-@ myapp :: xs:[a] -> ys:[a] -> {v:[a] | listElts(v) = Set_cup(listElts(xs), listElts(xs))} @-}
myapp :: [a] -> [a] -> [a]
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys

