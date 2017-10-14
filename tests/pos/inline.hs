{-@ LIQUID "--no-totality" @-}
module Fixme where

{-@ inline eqq @-}
eqq :: Ord a => a -> a -> Bool
eqq x y = x > y

{-@ eqqtest :: Eq a => x:a -> y:a -> {v:Bool | v <=> (eqq x y) } @-}
eqqtest :: Ord a => a -> a -> Bool
eqqtest x y = x > y

{-@ inline mymax @-}
mymax :: Ord a => a -> a -> a
mymax x y = if x >= y then x else y

{-@ inline mymin @-}
mymin :: Ord a => a -> a -> a
mymin x y = mymax y x

{-@ measure foo @-}
foo :: Ord a => D a -> a
foo (D x y) = mymax x y
foo (F x)   = x

{-@ measure bar @-}
bar :: Ord a => D a -> a
bar (D x y) = mymax x y

{-@ measure bar2 @-}
bar2 :: Ord a => D a -> a
bar2 (D x y) = mymin y x

foooo = D

data D a = D a a | F a

{-@ mymax3, mymax :: x:a -> y:a -> {v:a | v = mymax x y} @-}
mymax3 :: Ord a => a -> a -> a
mymax3 x y = if x >= y then x else y
