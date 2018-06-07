{-@ LIQUID "--noterm" @-}
module Tachio (main) where

{-@ chaos :: { True } @-}
chaos = False

-- should I increment b in the last arg?
{-@ suc :: b:Int ~> (v:{v>=b} -> ()) -> v:{v>=b} -> () @-}
suc :: (Int -> ()) -> Int -> ()
suc f x = f (x+1)

{-@ app3 :: a:Int ~> (v:{v>=a} -> ()) -> (((v:{v>=a} -> ())) -> ()) -> () @-}
app3 :: (Int -> ()) -> ((Int -> ()) -> ()) -> ()
app3 f g = if chaos then app3 (suc f) g else g f

{-@ check :: x:Int -> y:{x <= y} -> () @-}
check :: Int -> Int -> ()
check x y = ()

{-@ app :: a:Int -> (v:{v>=a} -> ()) -> () @-}
app :: Int -> (Int -> ()) -> ()
app x f = f x

main :: Int -> ()
main i = app3 (check i) (app i)
