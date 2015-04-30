module Append where


data L a = Nil | Cons a (L a)
{-@ measure append @-}
append :: L a -> L a -> L a
append xs Nil = xs
append xs (Cons y ys) = Cons y (append xs ys)