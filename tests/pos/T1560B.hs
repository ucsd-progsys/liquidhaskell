{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--extensionality" @-}

module T1560B where

k :: a -> b -> b
k _ b = b

{-@ reflect f @-}
f :: Int -> Int
f x = x + 1

{-@ reflect g @-}
g :: Int -> Int -> Int
g x = f

{-@ fgeqxy :: x:Int -> y:Int -> {f y = g x y} @-}
fgeqxy :: Int -> Int -> ()
fgeqxy x y = g x y `k` f y `k` ()

{-@ fgeqx :: x:Int -> {f = g x} @-}
fgeqx :: Int -> ()
fgeqx x = f `k` g x `k` ()
