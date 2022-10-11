{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--extensionality" @-}

module T1560 where

k :: a -> b -> b
k _ b = b

{-@ reflect f @-}
f :: Int -> Int -> Int
f x y = x + y

{-@ reflect g @-}
g :: Int -> Int -> Int
g = f

{-@ fgeqxy :: x:Int -> y:Int -> {f x y = g x y} @-}
fgeqxy :: Int -> Int -> ()
fgeqxy x y = g x y `k` f x y `k` ()

{-@ fgeqx :: x:Int -> {f x = g x} @-}
fgeqx :: Int -> ()
fgeqx x = f x `k` g x `k` ()

{-@ fgeq :: {f = g} @-}
fgeq :: ()
fgeq = f `k` g `k` ()
