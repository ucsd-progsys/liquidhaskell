module TC where

silly ::  Eq a => a -> a
silly x = if x == x then x else x

mmax ::  Ord a => a -> a -> a
mmax x y = if x > y then x else y

mabs ::  (Num a, Ord a) => a -> a
mabs x = if x > 0 then x else (-x)

x0 = mabs 4
x1 = mabs (-5)
z0 = mmax 2 8
z1 = mmax (3.2) (4.8)

