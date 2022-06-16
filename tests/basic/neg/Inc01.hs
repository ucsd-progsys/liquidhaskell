{-@ LIQUID "--expect-any-error" @-}
-- | Test 
module Inc01 where

{-@ inc :: {v:GHC.Types.Int | v >= 0} -> {v:GHC.Types.Int | v >= 0} @-}
inc :: Int -> Int 
inc x = plus x one


{-@ one :: {v:GHC.Types.Int | v >= 0} @-}
one :: Int 
one = undefined

{-@ plus :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Int| v = x - y} @-}
plus :: Int -> Int -> Int 
plus = undefined 

