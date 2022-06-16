{-@ LIQUID "--expect-any-error" @-}
module Inc02 where

{-@ inc :: {v:Int | v >= 0} -> {v:Int | v >= 0} @-}
inc :: Int -> Int 
inc x = x - 1
