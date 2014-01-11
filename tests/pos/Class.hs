{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--no-termination" @-}
module Class () where

import Language.Haskell.Liquid.Prelude
import Prelude hiding (sum, length, (!!), Functor(..))
import qualified Prelude as P

{-@ qualif Size(v:int, xs:a): v = (size xs) @-}

{-@ data List a = Nil | Cons (hd::a) (tl::(List a)) @-}
data List a = Nil | Cons a (List a)

{-@ length :: xs:List a -> {v:Nat | v = (size xs)} @-}
length :: List a -> Int
length Nil         = 0
length (Cons x xs) = 1 + length xs

{-@ (!!) :: xs:List a -> {v:Nat | v < (size xs)} -> a @-}
(!!) :: List a -> Int -> a
Nil         !! i = undefined
(Cons x _)  !! 0 = x
(Cons x xs) !! i = xs !! (i - 1)

{-@ class measure size :: forall a. a -> Int @-}
{-@ class Sized s where
      size :: forall a. x:s a -> {v:Nat | v = (size x)}
  @-}
class Sized s where
  size :: s a -> Int

instance Sized List where
  {-@ instance measure size :: List a -> Int
      size (Nil)       = 0
      size (Cons x xs) = 1 + (size xs)
    @-}
  size = length

instance Sized [] where
  {-@ instance measure size :: [a] -> Int
      size ([])   = 0
      size (x:xs) = 1 + (size xs)
    @-}
  size [] = 0
  size (x:xs) = 1 + size xs

{-@ class (Sized s) => Indexable s where
      index :: forall a. x:s a -> {v:Nat | v < (size x)} -> a
  @-}
class (Sized s) => Indexable s where
  index :: s a -> Int -> a


instance Indexable List where
  index = (!!)

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
      | otherwise = 0


{-@ x :: {v:List Int | (size v) = 3}  @-}
x :: List Int
x = 1 `Cons` (2 `Cons` (3 `Cons` Nil))

foo = liquidAssert $ size (Cons 1 Nil) == size [1]
