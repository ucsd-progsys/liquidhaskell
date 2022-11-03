module Abs where

abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ relational abs ~ abs :: { x1:Int -> Int 
                            ~ x2:Int -> Int 
                            | 0 <= x1 && x1 < x2 :=> r1 x1 < r2 x2 } @-}

{- relational abs ~ abs :: { x1:Int -> Int 
                            ~ x2:Int -> Int 
                            | 0 <= x1 && x1 Abs.(:=>) x2 N :=> r1 x1 < r2 x2 } @-}
