{-@ LIQUID "--reflection"       @-}
{-@ LIQUID "--ple"              @-}
{- LIQUID "--relational-hints" @-}
module RMemAlloc where

import RTick
import Prelude hiding (pure, foldl)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect foldl @-}
{-@ foldl :: (Int -> Int -> Int) -> Int -> xs:[Int] -> { t:Tick Int | tcost t == len xs } @-}
foldl :: (Int -> Int -> Int) -> Int -> [Int] -> Tick Int
foldl _ z [] = pure z
foldl f z (x : xs) = let w = f z x in 1 `step` foldl f w xs

{-@ reflect foldl' @-}
{-@ foldl' :: (Int -> Int -> Int) -> Int -> xs:[Int] -> { t:Tick Int | tcost t == 0 } @-}
foldl' :: (Int -> Int -> Int) -> Int -> [Int] -> Tick Int
foldl' _ z [] = pure z
foldl' f z (x : xs) = let w = f z x in w `seq` foldl' f w xs

{-@ relational foldl ~ foldl' :: { f1:(Int -> Int -> Int) -> acc1:Int -> xs1:[Int] -> Tick Int
                                 ~ f2:(Int -> Int -> Int) -> acc2:Int -> xs2:[Int] -> Tick Int
                                 | true :=> f1 = f2 && acc1 = acc2 :=> xs1 = xs2 
                                    :=> true } @-}

{-@ reflect length1 @-}
length1 :: [Int] -> Tick Int
length1 = foldl' upd 0 

{-@ reflect upd @-}
upd :: Int -> Int -> Int
upd x _ = x + 1 

{-@ reflect length2 @-}
length2 :: [Int] -> Tick Int
length2 = foldl upd 0 

{-@ relational length1 ~ length2 :: { xs1:[Int] -> Tick Int 
                                    ~ xs2:[Int] -> Tick Int 
                                    | xs1 = xs2 
                                        :=> RTick.tcost (RMemAlloc.length2 xs1) - RTick.tcost (RMemAlloc.length1 xs1) = len xs1} @-}

{-@ reflect len @-}
{-@ len :: [a] -> Nat @-}
len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + len xs
