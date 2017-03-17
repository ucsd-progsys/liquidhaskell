{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}
module Class () where

import Language.Haskell.Liquid.Prelude
import Prelude hiding (sum, length, (!!), Functor(..))
-- import qualified Prelude as P

{-@ qualif Size(v:Int, xs:a): v = size xs @-}

{-@ qualif Size(v:Int, xs:MList a): v = size xs @-}

{-@ data MList a = Nil | Cons (hd::a) (tl::(MList a)) @-}
data MList a = Nil | Cons a (MList a)

{-@ (!!) :: xs:MList a -> {v:Nat | v < (size xs)} -> a @-}
(!!) :: MList a -> Int -> a
Nil         !! _ = liquidError "impossible"
(Cons x _)  !! 0 = x
(Cons _ xs) !! i = xs !! (i - 1)

{-@ class measure size :: forall a. a -> Int @-}

{-@ class Sized s where
      size :: forall a. x:s a -> {v:Nat | v = size x}
  @-}
class Sized s where
  size :: s a -> Int

instance Sized MList where
  {-@ instance measure size :: MList a -> Int
      size (Nil)       = 0
      size (Cons x xs) = 1 + size xs
    @-}
  size = length

{-@ length :: xs:MList a -> {v:Nat | v = size xs} @-}
length :: MList a -> Int
length Nil         = 0
length (Cons _ xs) = 1 + length xs

{-@ bob :: xs:MList a -> {v:Nat | v = size xs} @-}
bob :: MList a -> Int
bob = length


instance Sized [] where
  {-@ instance measure size :: [a] -> Int
      size ([])   = 0
      size (x:xs) = 1 + (size xs)
    @-}
  size [] = 0
  size (_:xs) = 1 + size xs

{-@ class (Sized s) => Indexable s where
      index :: forall a. x:s a -> {v:Nat | v < size x} -> a
  @-}
class (Sized s) => Indexable s where
  index :: s a -> Int -> a


instance Indexable MList where
  index = (!!)

{-@ sum :: Indexable s => s Int -> Int @-}
sum :: Indexable s => s Int -> Int
sum xs = go max 0
  where
    max = size xs
    go (d::Int) i
      | i < max   = index xs i + go (d-1) (i+1)
      | otherwise = 0


{-@ sumMList :: MList Int -> Int @-}
sumMList :: MList Int -> Int
sumMList xs = go max 0
  where
    max = size xs
    go (d::Int) i
      | i < max   = index xs i + go (d-1) (i+1)
      | otherwise = 0


{-@ x :: {v:MList Int | (size v) = 3}  @-}
x :: MList Int
x = 1 `Cons` (2 `Cons` (3 `Cons` Nil))

foo = liquidAssert $ size (Cons 1 Nil) == size [1]
