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

{-@ identity :: f:(r -> a) -> { seq (pure id) (Reader f) == (Reader f) } @-}
identity :: (r -> a) ->  Proof
identity f 
  =   seq (pure id) (Reader f)
  ==! seq (Reader (\w -> id)) (Reader f)
  ==! Reader (\q -> ((\w -> id) q) (f q))
  ==! Reader (\q -> (id) (f q))
  ==! Reader (\q -> f q)
  ==! Reader f
  *** QED 
