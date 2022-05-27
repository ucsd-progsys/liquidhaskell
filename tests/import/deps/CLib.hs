module CLib where

import ALib
import BLib

{-@ quux :: x:Int -> y:Int -> z:Int -> {v:Int | v = x + y - z} @-}
quux :: Int -> Int -> Int -> Int
quux x y z = x `plus` y `minus` z
