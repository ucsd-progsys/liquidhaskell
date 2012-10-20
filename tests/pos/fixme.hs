module ListSetTest where

import Data.Set (Set(..))

{-@ include <listSet.hquals> @-}


-- WHY DOES THIS JUST NOT GET ANY MEANINGFUL TYPE?
{- goo :: xs:[a] 
       -> ys:[a] 
       -> {v:[a] | listElts(v) = Set_cup(listElts(xs), listElts(ys))} 
 @-}
goo :: [a] -> [a] -> [a]
goo acc []     = acc
goo acc (y:ys) = error "foo" -- goRev (y:acc) ys

{-@ choo :: [a] -> [a] @-}
choo :: [a] -> [a]
choo xs = goo [] xs









