{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--extensionality"  @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id, seq, pure)

import Proves
import Helper

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u

{-@ data Reader r a = Reader { runIdentity :: r -> a } @-}
data Reader r a     = Reader { runIdentity :: r -> a }


{-@ axiomatize pure @-}
pure :: a -> Reader r a
pure x = Reader (\r -> x)

{-@ axiomatize seq @-}
seq :: Reader r (a -> b) -> Reader r a -> Reader r b
seq (Reader f) (Reader x) = Reader (\r -> (f r) (x r))

{-@ axiomatize idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ axiomatize id @-}
id :: a -> a
id x = x


-- | Identity

{-@ identity :: x:Reader r a -> { seq (pure id) x == x } @-}
identity :: Reader r a -> Proof
identity (Reader r)
  =   seq (pure id) (Reader r)
  ==! seq (Reader (\w -> id)) (Reader r)
  ==! Reader (\q -> ((\w -> id) q) (r q))
  ==! Reader (\q -> (id) (r q))
  ==! Reader (\q -> r q)
  ==! Reader r 
  *** QED 


-- | Composition

{-@ composition :: x:Reader r (a -> a)
                -> y:Reader r (a -> a)
                -> z:Reader r a
                -> { (seq (seq (seq (pure compose) x) y) z) == seq x (seq y z) } @-}
composition :: Reader r (a -> a) -> Reader r (a -> a) -> Reader r a -> Proof
composition (Reader x) (Reader y) (Reader z)
  =   seq (seq (seq (pure compose) (Reader x)) (Reader y)) (Reader z) 
  ==! seq (seq (seq (Reader (\r1 -> compose)) (Reader x)) (Reader y)) (Reader z)
  ==! seq (seq (Reader (\r2 -> ((\r1 -> compose) r2) (x r2))) (Reader y)) (Reader z)
  ==! seq (seq (Reader (\r2 -> compose (x r2))) (Reader y)) (Reader z)
  ==! seq (Reader (\r3 -> ((\r2 -> compose (x r2)) r3) (y r3))) (Reader z)
  ==! seq (Reader (\r3 -> (compose (x r3)) (y r3))) (Reader z)
  ==! Reader (\r4 -> ((\r3 -> (compose (x r3)) (y r3)) r4) (z r4)) 
  ==! Reader (\r4 -> (compose (x r4) (y r4)) (z r4)) 
  ==! Reader (\r4 -> (x r4) ((y r4) (z r4)))
  ==! Reader (\r4 -> (x r4) ((\r5 -> (y r5) (z r5)) r4))
  ==! seq (Reader x) (Reader (\r5 -> (y r5) (z r5)))
  ==! seq (Reader x) (seq (Reader y) (Reader z))
  *** QED 


-- | homomorphism  pure f <*> pure x = pure (f x)

{- homomorphism :: f:(a -> a) -> x:a
                 -> { seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  =   seq (pure f) (pure x)
  ==! seq (Reader (\r2 -> f)) (Reader (\r2 -> x))
  ==! Reader (\r -> ((\r2 -> f) r ) ((\r2 -> x) r))
  ==! Reader (\r -> f x)
  ==! pure (f x)
  *** QED 

{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 
 