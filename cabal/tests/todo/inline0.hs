module Goo (plus) where

{-# INLINE incr #-}
incr :: Int -> Int
incr x = x + 1

poo x = incr x

plus x = incr x
