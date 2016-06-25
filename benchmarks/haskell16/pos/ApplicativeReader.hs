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

{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 
 