module ReWrite10 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--rw-termination-check" @-}
{-@ infix ++ @-}

import Prelude hiding (length, (++))

data N = S N | Z


{-@ lazy    f @-}
{-@ reflect f @-}
f :: N -> N
f x = g x

{-@ lazy    g @-}
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

