module Goo where 

import Data.Set (Set(..))  

{-@ myid1 :: xs:[a] -> {v:[a]| (listElts v) = (listElts xs)} @-}
myid1 []     = []
myid1 (x:xs) = x : myid1 xs


{-@ myid :: xs:[a] -> {v:[a]| (len v) = (len xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs


