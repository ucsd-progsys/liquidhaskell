module Gradual where
 
{-@ LIQUID "--gradual"        @-}
{-@ LIQUID "--savequery"      @-}
 
{-@ safe :: {v:Int | ?? } -> Int @-}
safe   :: Int ->  Int
safe x = if foo () then bar1 x else bar2 x
 
{-@ foo :: () -> {v:Bool | true } @-} 
foo :: () -> Bool 
foo = undefined 

{-@ bar1 :: {v:Int | v < 0 } -> Int @-}
bar1   :: Int -> Int 
bar1 x = x 

{-@ bar2 :: {v:Int | v = 0} -> Int @-}
bar2 :: Int -> Int 
bar2 x = x