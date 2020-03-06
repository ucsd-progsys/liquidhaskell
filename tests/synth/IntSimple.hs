{-@ LIQUID "--typed-holes" @-}

module IntSimple where

import Language.Haskell.Liquid.Synthesize.Error

{-@ plus :: x: Int -> y: Int -> { v: Int | v == x + y } @-}
plus :: Int -> Int -> Int 
plus x y = x + y

{-@ one :: { v: Int | v == 1} @-}
one :: Int
one = 1

{-@ zero :: { v: Int | v == 0 } @-}
zero :: Int 
zero = 0

{-@ measure length' @-}
{-@ length' :: [a] -> Nat @-}
length' :: [a] -> Int
length' [] = 0
length' (x:xs) = 1 + length' xs

{-@ foo :: x: Int -> { v: Int | v == x + 1 } @-}
next :: Int -> Int
next = _goal
