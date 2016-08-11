{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}
module Class () where

import Language.Haskell.Liquid.Prelude
import Prelude hiding (sum, length, (!!), Functor(..))

{- qualif Size(v:Int, xs:a): v = size xs @-}
{- qualif Size(v:Int, xs:MList a): v = size xs @-}

data MList a = Nil | Cons a (MList a)

{-@ (!!) :: xs:MList a -> {v:Nat | v < sz xs} -> a @-}
(!!) :: MList a -> Int -> a
(Cons x _)  !! 0 = x
(Cons _ xs) !! i = xs !! (i - 1)

{-@ class measure sz :: forall a. a -> Int  @-}

{-@ class Sized s where
      size :: forall a. x:s a -> {v:Nat | v = sz x}
  @-}
class Sized s where
  size :: s a -> Int

instance Sized MList where
  {-@ instance measure sz :: MList a -> Int
      sz (Nil)       = 0
      sz (Cons x xs) = 1 + sz xs
    @-}
  size = length

{-@ length :: xs:MList a -> {v:Nat | v = sz xs} @-}
length :: MList a -> Int
length Nil         = 0
length (Cons _ xs) = 1 + length xs

{-@ bob :: xs:MList a -> {v:Nat | v = sz xs} @-}
bob :: MList a -> Int
bob = length


instance Sized [] where
  {-@ instance measure sz :: [a] -> Int
      sz ([])   = 0
      sz (x:xs) = 1 + (sz xs)
    @-}
  size [] = 0
  size (_:xs) = 1 + size xs

{-@ class (Sized s) => Indexable s where
      index :: forall a. x:s a -> {v:Nat | v < sz x} -> a
  @-}
class (Sized s) => Indexable s where
  index :: s a -> Int -> a



instance Indexable MList where
  index = (!!)

{-@ sum :: Indexable s => s Int -> Int @-}
sum :: Indexable s => s Int -> Int
sum xs = go n 0
  where
    n = size xs
    go (d::Int) i
      | i < n     = index xs i + go (d-1) (i+1)
      | otherwise = 0


{-@ sumMList :: MList Int -> Int @-}
sumMList :: MList Int -> Int
sumMList xs = go max 0
  where
    max = size xs
    go (d::Int) i
      | i < max   = index xs i + go (d-1) (i+1)
      | otherwise = 0


{-@ mlist3 :: {v:MList Int | sz v = 3}  @-}
mlist3 :: MList Int
mlist3 = 1 `Cons` (2 `Cons` (3 `Cons` Nil))

foo = liquidAssert $ size (Cons 1 Nil) == size [1]
