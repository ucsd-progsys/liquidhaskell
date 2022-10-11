{-@ LIQUID "--expect-any-error" @-}
-- | Test 
module Inc01q where

{-@ inc :: {v:Int | v >= 0} -> {v:Int | v >= 0} @-}
inc :: Int -> Int 
inc x = plus x one

{-@ one :: {v:Int | v >= 0} @-}
one :: Int 
one = undefined

{-@ plus :: x:Int -> y:Int -> {v:Int| v = x - y} @-}
plus :: Int -> Int -> Int 
plus = undefined 

