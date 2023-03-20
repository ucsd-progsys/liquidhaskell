{- LIQUID "--relational-hints" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module RPatError where

import Prelude hiding (zip)

{-@ measure len @-}
{-@ len :: [a] -> Nat @-}
len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + len xs

{-@ reflect zip @-}
{-@ zip :: xs:[Int] -> {ys:[Int]|ys = xs} -> () @-}
zip :: [Int] -> [Int] -> ()
zip [] [] = ()
zip (_:xs) (_:ys) = zip xs ys

{-@ relational zip ~ zip :: { xs1:[Int] -> ys1:[Int] -> ()
                            ~ xs2:[Int] -> ys2:[Int] -> ()
                            | true :=> ys1 = xs1 && ys2 = xs2 :=> true } @-}