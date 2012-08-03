module Foo (llen) where

{-# INLINE ffoldr #-}
ffoldr     :: (a -> b -> b) -> b -> [a] -> b
ffoldr k z = go
          where
            go []     = z
            go (y:ys) = y `k` go ys

llen :: [a] -> Int
llen = ffoldr (\_ n -> n + 1) 0 
