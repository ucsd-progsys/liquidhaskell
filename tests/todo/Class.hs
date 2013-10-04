{-@ LIQUID "--no-termination" @-}
module Class where

import Prelude hiding (sum)

class Sized s where
  {-@ class measure size :: Sized s => s a -> Int @-}

  {-@ size :: Sized s => x:s a -> {v:Int | v = (size x)} @-}
  size :: s a -> Int

instance Sized [] where
  {-@ instance measure size [] = len @-}
  -- length <: size[[]/s][len/size]
  size = length


class (Sized s) => Indexable s where
  {-@ index :: Indexable s => x:s a -> {v:Nat | v < (size x)} -> a @-}
  index :: s a -> Int -> a

instance Indexable [] where
  -- (!!) <: index[[]/s][len/size]
  index = (!!)



{-@ sum :: Indexable s => s Int -> Int @-}
sum :: Indexable s => s Int -> Int
sum xs = go 0
  where
    -- max :: {v:Int | v = size xs}
    max = size xs
    go i
                    -- i :: {v:Nat | v < size xs}
      | i < max   = index xs i + go (i+1)
      | otherwise = 0


{-@ sumList :: [Int] -> Int @-}
sumList :: [Int] -> Int
sumList xs = go 0
  where
    -- max :: {v:Int | v = len xs}
    max = size xs
    go i
                    -- i :: {v:Nat | v < len xs}
      | i < max   = index xs i + go (i+1)
      | otherwise = 0
