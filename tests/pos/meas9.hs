module Meas where

import Data.Set (Set(..))

{-@ measure listElts :: forall a. [a] -> (Set a)
    listElts([])   = {v | (? Set_emp(v))}
    listElts(x:xs) = {v | v = Set_cup(Set_sng(x), listElts(xs)) }
  @-}

{-@ myapp :: xs:[a] -> ys:[a] -> {v:[a]| listElts(v) = Set_cup(listElts(xs), listElts(ys))} @-}
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys

