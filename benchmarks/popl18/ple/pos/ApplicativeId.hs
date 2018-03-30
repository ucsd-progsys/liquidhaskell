{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id, pure, seq)

import Language.Haskell.Liquid.ProofCombinators


-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ reflect pure @-}
pure :: a -> Identity a
pure x = Identity x

{-@ reflect seq @-}
seq :: Identity (a -> b) -> Identity a -> Identity b
seq (Identity f) (Identity x) = Identity (f x)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ data Identity a = Identity { runIdentity :: a } @-}
data Identity a = Identity a

-- | Identity
{-@ identity :: x:Identity a -> { seq (pure id) x == x } @-}
identity :: Identity a -> Proof
identity (Identity x)
  =   trivial 

-- | Composition

{-@ composition :: x:Identity (a -> a)
                -> y:Identity (a -> a)
                -> z:Identity a
                -> { (seq (seq (seq (pure compose) x) y) z) == seq x (seq y z) } @-}
composition :: Identity (a -> a) -> Identity (a -> a) -> Identity a -> Proof
composition (Identity x) (Identity y) (Identity z)
  =   trivial 

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> { seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  =   trivial 

interchange :: Identity (a -> a) -> a -> Proof
{-@ interchange :: u:(Identity (a -> a)) -> y:a
     -> { seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange (Identity f) x
  =   trivial 
