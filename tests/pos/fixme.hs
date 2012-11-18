module Goo where 

-- import Data.Set (Set(..))  

{- myid :: xs:[a] -> {v:[a]| listElts(v) = listElts(xs)} @-}
-- myid :: [b] -> [b]

{-@ myid :: xs:[a] -> {v:[a]| len(v) = len(xs)} @-}
-- myid :: [b] -> [b]
myid []     = []
myid (x:xs) = x : myid xs


