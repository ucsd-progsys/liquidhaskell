module Test () where

{-@ posPlus :: x:{v: Int | v >= 0} -> {v: Int | v >= x} @-}
posPlus :: Int -> Int
posPlus x = if (x > 0) 
              then 2 + (posPlus (x - 1))
              else 0

goo = posPlus (-3)

{-@ poo :: x:Int -> {v: Int | v >= x } @-}
poo x = if x > 0 then posPlus x else x

