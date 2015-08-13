module Append where


{-@ LIQUID "--no-termination" @-}

{- Cons :: y:a -> ys: L a -> {v:L a | v = Cons y ys} @-}

data L a = Nil | Cons a (L a)
{-@ measure append @-}
append :: L a -> L a -> L a
append xs Nil = xs
append xs (Cons y ys) = Cons y (append xs ys)
