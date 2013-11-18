module Termination where

import Prelude hiding (sum, (!!), repeat)
import Data.List      (lookup)
import Data.Maybe     (fromJust)

import Language.Haskell.Liquid.Prelude (liquidAssert)

-- | Termination Check with Refinement Types

type Val   = Int
data Vec   = V [(Int, Val)]

(!!)       :: Vec -> Int -> Val
(V a) !! i = case i `lookup` a of {Just v -> v; _ -> 0}


{-@ sum :: Vec -> Nat -> Val @-}
sum     :: Vec -> Int -> Val
sum a 0 = 0
sum a i = (a !! (i-1)) + sum a (i-1)

-- | Choosing the correct argument

{-@ sum' :: Vec -> Val -> Nat -> Val @-}
{-@ Decrease sum' 3 @-}
sum' :: Vec -> Val -> Int -> Val
sum' a acc 0 = acc + a!!0 
sum' a acc i = sum' a (acc + a!!i) (i-1)

-- | Lexicographic Termination

data Vec2D    = V2D [((Int, Int), Val)]

(!!!)         :: Vec2D -> (Int,Int) -> Val
(V2D a) !!! i = case i `lookup` a of {Just v -> v; _ -> 0}

{-@ sum2D :: Vec2D -> Nat -> Nat -> Val @-}
sum2D :: Vec2D -> Int -> Int -> Val
sum2D a n m = go n m
  where 
       {-@ go :: i:Nat -> j:Nat -> Val / [i, j] @-}
       {-@ Decrease go 1 2 @-}
        go 0 0             = 0
        go i j | j == 0    =  a!!!(i, 0) + go (i-1) m
               | otherwise =  a!!!(i, j) + go i (j-1)

-- | Decreasing expressions

{-@ sumFromTo :: Vec -> lo:Nat -> hi:{v:Nat|v>=lo} -> Val @-}
sumFromTo :: Vec -> Int -> Int ->  Val
sumFromTo a lo hi = go lo hi
  where 
       {-@ go :: lo:Nat -> hi:{v:Nat|v>=lo} -> Val / [hi-lo] @-}
        go lo hi | lo == hi  =  a!!lo
                 | otherwise =  a!!lo + go (lo+1) hi

-- | Why is Termination Analysis Required

{-@ Lazy foo @-}
{-@ foo :: Int -> {v:Int | false} @-}
foo     :: Int -> Int
foo n   = foo n

prop = liquidAssert ((\_ -> 0==1) (foo 0))

-- | Turning off Termination Checking

{-@ Lazy repeat @-}
{-@ repeat :: a -> [a] @-}
repeat     :: a -> [a]
repeat a   = a : repeat a
