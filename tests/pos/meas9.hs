module Meas where

import Data.Set (Set(..))

{-@ myapp :: xs:[a] -> ys:[a] -> {v:[a]| listElts(v) = Set_cup(listElts(xs), listElts(ys))} @-}
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys

