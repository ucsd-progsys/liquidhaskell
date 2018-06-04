{-@ LIQUID "--noterm" @-}
module Tachio (main) where

{-@ chaos :: { True } @-}
chaos = undefined

suc f x = f (x+1)

app3 f g = if chaos then app3 (suc f) g else g f

{-@ check :: x:Int -> y:{x <= y} -> () @-}
check :: Int -> Int -> ()
check x y = ()

app x f = f x

main :: Int -> ()
main i = app3 (check i) (app i)
