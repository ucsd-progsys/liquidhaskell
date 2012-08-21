module Foo where

moo = insert 4 [1, 2, 0]


{-@ assert insert      :: (Ord a) => x:a -> xs: [a]<{v: a | (v >= fld)}> -> {v: [a]<{v: a | (v >= fld)}> | len(v) = (1 + len(xs)) } @-}
insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs


