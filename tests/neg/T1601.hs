{-@ LIQUID "--reflect" @-}
{-@ LIQUID "--ple" @-}
{-@ reflect g @-}
g :: b -> c -> c
g y z = z
{-@ reflect f @-}
f :: a -> b -> b
f x y  = g (g x y) y

k :: a -> b -> b
k _ b = b

{-@ fgeq :: x:a -> {f x == g x} @-}
fgeq :: a -> b -> ()
fgeq _ _ = ()
