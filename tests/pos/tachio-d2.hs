module Tachio (main) where

{-@ chaos :: { True } @-}
chaos = undefined

{-@ app :: a:Int ~> (v:{v>=a} -> ()) -> {v:Int | v=a} -> () @-}
app :: (Int -> ()) -> Int -> ()
app f x = if chaos then app f (x + 1) else f x

{-@ check :: x:Int -> y:{x <= y} -> () @-}
check :: Int -> Int -> ()
check x y = ()

main :: Int -> ()
main i = app (check i) i
