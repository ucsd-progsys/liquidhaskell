{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}
module Class where

import Prelude hiding (sum, length, (!!), Functor(..))
import qualified Prelude as P
{-@ qualif Diff(v:int,l:int,i:int): v = l - i @-}

data List a = Nil | Cons a (List a)
{-@ data List a = Nil | Cons (hd::a) (tl::(List a)) @-}


{-@ length :: xs:List a -> {v:Nat | v = (size xs)} @-}
length :: List a -> Int
length Nil         = 0
length (Cons x xs) = 1 + length xs

{-@ (!!) :: xs:List a -> {v:Nat | v < (size xs)} -> a @-}
(!!) :: List a -> Int -> a
Nil         !! i = undefined
(Cons x _)  !! 0 = x
(Cons x xs) !! i = xs !! (i - 1)

class Sized s where
  {-@ class measure size :: forall a. a -> Int @-}

  {- size :: Sized s => forall a. x:s a -> {v:Int | v = (size x)} @-}
  size :: s a -> Int

instance Sized List where
  {-@ instance measure size :: List a -> Int
      size (Nil)       = 0
      size (Cons x xs) = 1 + (size xs)
    @-}
  -- length <: size[[]/s][len/size]
  size = length


class (Sized s) => Indexable s where
  {-@ index :: Indexable s => forall a. x:s a -> {v:Nat | v < (size x)} -> a @-}
  index :: s a -> Int -> a

instance Indexable List where
  -- (!!) <: index[[]/s][len/size]
  {-@ $cindex :: forall a. x:List a -> {v:Nat | v < (size x)} -> a @-}
  index = (!!)

instance Sized [] where
  size = P.length
instance Indexable [] where
  index xs i = xs P.!! i

class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor List where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

instance P.Functor List where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (P.fmap f xs)

{-@ sum :: Indexable s => s Int -> Int @-}
sum :: Indexable s => s Int -> Int
sum xs = go max 0
  where
    max = size xs
    go (d::Int) i
      | i < max   = index xs i + go (d-1) (i+1)
      | otherwise = 0


{-@ sumList :: List Int -> Int @-}
sumList :: List Int -> Int
sumList xs = go max 0
  where
    max = size xs
    go (d::Int) i
      | i < max   = index xs i + go (d-1) (i+1)
      | otherwise = index xs i


{-@ x :: {v:List Int | (size v) = 3}  @-}
x :: List Int
x = 1 `Cons` (2 `Cons` (3 `Cons` Nil))
