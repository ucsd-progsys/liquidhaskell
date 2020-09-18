{-@ LIQUID "--reflection" @-}
module T871 where

{-@ data Vec [vlen] t = Nil | Cons {td :: t, tl :: Vec t} @-}
data Vec t = Nil | Cons t (Vec t)

{-@ reflect vlen @-}
vlen :: Vec t -> Int
vlen Nil = 0
vlen (Cons _ ts) = 1 + vlen ts

{-@ data Vec2 [vlen2] t = Nil2 | Cons2 t (Vec2 t) @-}
data Vec2 t = Nil2 | Cons2 t (Vec2 t)

{-@ reflect vlen2 @-}
vlen2 :: Vec2 t -> Int
vlen2 Nil2 = 0
vlen2 (Cons2 _ ts) = 1 + vlen2 ts
