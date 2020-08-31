module ReWrite10 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--rw-termination-check" @-}
{-@ infix ++ @-}

import Prelude hiding (length, (++))

data N = S N | Z
{-@ data N [toInt] @-}


{-@ reflect toInt @-}
toInt :: N -> Int 
{-@ toInt :: N -> {v:Int | 0 <= v  } @-}
toInt Z     = 0 
toInt (S n) = 1 + toInt n 

{-@ reflect f @-}
{-@ f :: x:N -> N /[toInt x, 1]@-}
f :: N -> N
f x = g x

{-@ reflect g @-}
{-@ g :: x:N -> N / [toInt x, 0] @-}
g :: N -> N
g (S x) = f x
g Z     = Z

{-@ rewrite diverge @-}
{-@ assume diverge :: x : N -> { f x = g (S (S x)) } @-}
diverge :: N -> ()
diverge _ = ()

{-@ proof :: x : N -> {g x = f x} @-}
proof :: N -> ()
proof _ = ()

