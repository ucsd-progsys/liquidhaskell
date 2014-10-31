module Crash where

{-@ f :: (Num a) => {v:a | v > 0.0} -> a @-}
f :: (Num a) => a -> a
f a = a + 1

{-@ g :: (Num a) => {v:a | v > 0.0} -> a @-}
g :: (Num a) => a -> a
g = f
