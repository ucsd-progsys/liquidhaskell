module Grty2 () where

moo = insert 4 [1, 2, 3]

{-@ insert      :: (Ord a) => x:a -> xs: [a]<{\fld v -> (v >= fld)}> -> {v: [a]<{\fld v -> (v >= fld)}> | len(v) = (1 + len(xs)) } @-}
insert y []                            = [y]
insert y (x : xs) | y > {- <= -} x     = y : x : xs 
                  | otherwise          = x : insert y xs

