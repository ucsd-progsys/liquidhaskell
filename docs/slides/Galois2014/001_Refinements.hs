{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module Refinements where

import Prelude hiding (map, foldr, foldr1)

divide    :: Int -> Int -> Int
-----------------------------------------------------------------------
-- | Our first Data Type
-----------------------------------------------------------------------

data List a = N | C a (List a)

infixr 9 `C`

-----------------------------------------------------------------------
-- | A few Higher-Order Functions
-----------------------------------------------------------------------

map                  :: (a -> b) -> List a -> List b
map f N              = N
map f (C x xs)       = C (f x) (map f xs) 


foldr                :: (a -> b -> b) -> b -> List a -> b 
foldr f acc N        = acc
foldr f acc (C x xs) = f x (foldr f acc xs)


-- Uh oh. How shall we fix the error? Lets move on for now...

foldr1           :: (a -> a -> a) -> List a -> a   
foldr1 f (C x xs)    = foldr f x xs
foldr1 f N           = die "foldr1"


-----------------------------------------------------------------------
-- | Measuring the Size of Data
-----------------------------------------------------------------------

{-@ measure size @-}
size          :: List a -> Int
size (C x xs) = 1 + size xs 
size N        = 0


append N        ys = ys
append (C x xs) ys = C x (append xs ys)


-----------------------------------------------------------------------
-- | But there are limitations: why does this not work? ...
-----------------------------------------------------------------------

{-@ append' :: xs:_ -> ys:_ -> {v: _ | size v = size xs + size ys} @-}
append' xs ys =  foldr C ys  xs




-----------------------------------------------------------------------
-- | Definitions from 000_Refinements.hs
-----------------------------------------------------------------------

{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ divide :: Int -> NonZero -> Int @-}
divide x 0 = die "divide-by-zero"
divide x n = x `div` n

-----------------------------------------------------------------------
-- | CHEAT AREA 
-----------------------------------------------------------------------

-- # START-ERRORS 3 (foldr1, wtAverage, append')
-- # END-ERRORS   1 (append')

{- map    :: _ -> xs:_ -> {v:_ | size v = size xs}               @-}
{- append :: xs:_ -> ys:_ -> {v: _ | size v = size ys + size xs} @-}
{- foldr1 :: (a -> a -> a) -> {v:List a | size v > 0} -> a       @-}   
