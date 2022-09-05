module T2076 where 

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@
reflect f1 
f1 :: f:(Int -> Int) -> x:Int -> { v:Int | v = f x }
@-}
f1 :: (Int -> Int) -> Int -> Int
f1 f x = f x

{-@
f2 :: w:Int -> { u:Int | u == w } 
@-}
f2 :: Int -> Int
f2 y = f1 (\x -> x + 1)  (y - 1)
