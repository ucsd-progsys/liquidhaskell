{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id, pure, seq)

import Proves
import Helper

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ axiomatize pure @-}
pure :: a -> Identity a
pure x = Identity x

{-@ axiomatize seq @-}
seq :: Identity (a -> b) -> Identity a -> Identity b
seq (Identity f) (Identity x) = Identity (f x)

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ data Identity a = Identity { runIdentity :: a } @-}
data Identity a = Identity a

-- | Identity
{-@ identity :: x:Identity a -> { seq (pure id) x == x } @-}
identity :: Identity a -> Proof
identity (Identity x)
  =   seq (pure id) (Identity x)
  ==! seq (Identity id) (Identity x)
  ==! Identity (id x)
  ==! Identity x
  *** QED

-- | Composition

{-@ composition :: x:Identity (a -> a)
                -> y:Identity (a -> a)
                -> z:Identity a
                -> { (seq (seq (seq (pure compose) x) y) z) == seq x (seq y z) } @-}
composition :: Identity (a -> a) -> Identity (a -> a) -> Identity a -> Proof
composition (Identity x) (Identity y) (Identity z)
  =   seq (seq (seq (pure compose) (Identity x)) (Identity y)) (Identity z)
  ==! seq (seq (seq (Identity compose) (Identity x)) (Identity y)) (Identity z)
  ==! seq (seq (Identity (compose x)) (Identity y)) (Identity z)
  ==! seq (Identity (compose x y)) (Identity z)
  ==! Identity (compose x y z)
  ==! seq (Identity x) (Identity (y z))
  ==! seq (Identity x) (seq (Identity y) (Identity z))
  *** QED

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> { seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  =   seq (pure f) (pure x)
  ==! seq (Identity f) (Identity x)
  ==! Identity (f x)
  ==! pure (f x)
  *** QED

interchange :: Identity (a -> a) -> a -> Proof
{-@ interchange :: u:(Identity (a -> a)) -> y:a
     -> { seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange (Identity f) x
  =   seq (Identity f) (pure x)
  ==! seq (Identity f) (Identity x)
  ==! Identity (f x)
  ==! Identity ((idollar x) f)
  ==! seq (Identity (idollar x)) (Identity f)
  ==! seq (pure (idollar x)) (Identity f)
  *** QED
