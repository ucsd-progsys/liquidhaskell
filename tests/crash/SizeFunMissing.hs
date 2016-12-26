{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--exactdc"             @-}

module MapReduce where

import Prelude hiding (mconcat, map, split, take, drop, sum)
import Language.Haskell.Liquid.ProofCombinators

{-@ data List [llen] a = N | C {lhead :: a, ltail :: List a} @-}
data List a = N | C a (List a)

{-@ measure llen @-}
llen :: List a -> Bool 
llen N = True  
llen (C _ xs) = False -- 1 + llen xs

{-@ axiomatize sum @-}
sum  :: List Int -> Int
sum N        = 0
sum (C x xs) = x `plus` sum xs

{-@ axiomatize plus @-}
plus :: Int -> Int -> Int
plus x y = x + y

{-@ axiomatize msum @-}
msum :: List Int -> Int
msum is = sum is