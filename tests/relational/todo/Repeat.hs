module Fixme where

import           Prelude                 hiding ( sum )

data List a = Nil | Cons a (List a)

{-@ type Repeat a X = List {v:a | v == X} @-}

{-@ aps :: x:Int -> Repeat Int x -> Int @-}
aps :: Int -> List Int -> Int
aps _ Nil         = 0
aps a (Cons x xs) = x + aps a xs

{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size :: List a -> Int
size Nil         = 0
size (Cons _ xs) = 1 + size xs

{-@ relational aps ~ aps :: x1:Int -> l1:Repeat Int x1 -> Int ~ x2:Int -> l2:Repeat Int x2 -> Int
                         | x1 < x2 => true => len l1 == len l2 && r1 x1 l1 < r2 x2 l2 @-}
