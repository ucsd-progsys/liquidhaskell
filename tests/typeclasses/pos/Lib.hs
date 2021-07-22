{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
module Lib where
{-@ data List a = Nil | Cons {lh::a, lt::List a} @-}
data List a = Nil | Cons a (List a)

{-@ reflect foldrList @-}
foldrList :: (a -> b -> b) -> b -> List a -> b
foldrList _ x Nil         = x
foldrList f x (Cons y ys) = f y (foldrList f x ys)

{-@ reflect foldlList @-}
foldlList :: (b -> a -> b) -> b -> List a -> b
foldlList _ x Nil         = x
foldlList f x (Cons y ys) = foldlList f (f x y) ys


{-@ data NonEmpty a = NonEmpty {neh::a, net:: (List a)} @-}
data NonEmpty a = NonEmpty a (List a)

{-@ reflect head' @-}
head' :: NonEmpty a -> a
head' (NonEmpty a _) = a

{-@ reflect tail' @-}
tail' :: NonEmpty a -> List a
tail' (NonEmpty _ t) = t
