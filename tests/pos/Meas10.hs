module Meas10 where

import qualified Data.Set as S 

import Language.Haskell.Liquid.Prelude

{-@ myrev :: xs:[a] -> {v:[a] | S.listElts v = S.listElts xs} @-}
myrev :: [a] -> [a]
myrev xs = go [] xs 
   where 
      go acc []     = acc
      go acc (y:ys) = go (y:acc) ys

-- WHY DOES THIS JUST NOT GET ANY MEANINGFUL TYPE?
{-@ goo :: xs:[a] -> ys:[a] -> {v:[a] | S.listElts v = S.union (S.listElts xs) (S.listElts ys) } @-}
goo :: [a] -> [a] -> [a]
goo acc []     = acc
goo acc (y:ys) = unsafeError "foo" -- goRev (y:acc) ys

{-@ emptySet :: a -> {v:[b] | S.listElts v == S.empty } @-}
emptySet :: a -> [b]
emptySet x = []
