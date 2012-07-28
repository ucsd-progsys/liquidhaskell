{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP,  MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
   mylen
  ) where

import GHC.Base hiding (assert) 

{-# INLINE mfoldr #-}
mfoldr :: (a -> b -> b) -> b -> [a] -> b
mfoldr k z = go 
  where go []     = z
        go (y:ys) = y `k` go ys

{-@ assert mylen :: xs: [a] -> {v: Int | v = len(xs)} @-}
mylen :: [a] -> Int
mylen = mfoldr (\_ -> (1 +)) 0

--{-# INLINE mmap #-}
--mmap f = go 
--  where go []     = []
--        go (x:xs) = (f x) : (go xs)
--
--myadd :: [Int] -> [Int]
--myadd = mmap (1 +)








