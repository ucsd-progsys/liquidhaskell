{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Adt0 where

{-@ data Vec a = Nil | Cons { vHead :: a, vTail :: Vec a } @-}
data Vec a = Nil | Cons { vHead :: a, vTail :: Vec a }

{-@ prop :: xs:(Vec a) -> y:a -> ys:(Vec a) -> {v:() | xs == Cons y ys} -> {y == vHead xs} @-}
prop :: Vec a -> a -> Vec a -> () -> ()
prop x y zs _ = ()

{-@ zop :: x:a -> xs:Vec a -> { Cons x xs /= Nil } @-}
p
zop :: a -> Vec a -> ()
zop x xs = ()
