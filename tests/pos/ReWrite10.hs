module ReWrite10 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding (length, (++))

data N = S N | Z


{-@ reflect f @-}
f :: N -> N
f x = g x

{-@ reflect g @-}
g (S x) = f x
g Z     = Z

{-@ rewrite diverge @-}
{-@ assume diverge :: x : N -> { f x = g (S (S x)) } @-}
diverge :: N -> ()
diverge _ = ()

{-@ proof :: x : N -> {g x = f x} @-}
proof :: N -> ()
proof _ = ()

