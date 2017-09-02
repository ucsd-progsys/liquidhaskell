module Blank where

{-@ type Geq X = {v:Int | X <= v} @-} 

{-@ thisOk :: x:Int -> y:{Int | y > 10}  -> () @-}
thisOk :: Int -> Int -> ()
thisOk = undefined 

{-@ thisBad1 :: x:Int -> y:Geq y  -> () @-}
thisBad1 :: Int -> Int -> ()
thisBad1 = undefined 

{-@ thisBad2 :: x:Int -> y:{y > 10}  -> () @-}
thisBad2 :: Int -> Int -> ()
thisBad2 = undefined 
