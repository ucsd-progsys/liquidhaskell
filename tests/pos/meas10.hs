module Meas where

import Data.Set (Set(..))

{-@ include <listSet.hquals> @-}

{-@ myrev :: xs:[a] -> {v:[a]| listElts(v) = listElts(xs)} @-}
myrev :: [a] -> [a]
myrev xs = goRev [] xs 
--   where go acc []     = acc
--         go acc (y:ys) = go (y:acc) ys

-- WHY DOES THIS JUST NOT GET ANY MEANINGFUL TYPE?
{- goo :: xs:[a] -> ys:[a] -> {v:[a] | listElts(v) = Set_cup(listElts(xs), listElts(ys))} @-}
goo :: [a] -> [a] -> [a]
goo acc []     = acc
goo acc (y:ys) = error "foo" -- goRev (y:acc) ys

-- WORKS WITH EXPLICIT ANNOTATION
{- goRev :: xs:[a] -> ys:[a] -> {v:[a] | listElts(v) = Set_cup(listElts(xs), listElts(ys))} @-}
goRev :: [a] -> [a] -> [a]
goRev acc []     = acc
goRev acc (y:ys) = goRev (y:acc) ys

{-@ emptySet :: a -> {v:[b] | Set_emp(listElts(v))} @-}
emptySet :: a -> [b]
emptySet x = []
