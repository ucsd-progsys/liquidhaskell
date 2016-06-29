{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--extensionality"  @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module MonadMaybe where

import Prelude hiding (return, Maybe(..), (>>=))

import Proves
import Helper

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ axiomatize return @-}
return :: a -> Identity a
return x = Identity x

{-@ axiomatize bind @-}
bind :: Identity a -> (a -> Identity b) -> Identity b
bind (Identity x) f = f x

{-@ data Identity a = Identity { runIdentity :: a } @-}
data Identity a = Identity a

-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> Identity b) -> { bind (return x) f == f x } @-}
left_identity :: a -> (a -> Identity b) -> Proof
left_identity x f
  =   bind (return x) f
  ==! bind (Identity x) f
  ==! f x
  *** QED



-- | Right Identity

{-@ right_identity :: x:Identity a -> { bind x return == x } @-}
right_identity :: Identity a -> Proof
right_identity (Identity x)
  =   bind (Identity x) return
  ==! return x
  ==! Identity x
  *** QED


-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ associativity :: m:Identity a -> f: (a -> Identity b) -> g:(b -> Identity c)
  -> {bind (bind m f) g == bind m (\x:a -> (bind (f x) g)) } @-}
associativity :: Identity a -> (a -> Identity b) -> (b -> Identity c) -> Proof
associativity (Identity x) f g
  =   bind (bind (Identity x) f) g
  ==! bind (f x) g
  ==! (\x -> (bind (f x) g)) x
  ==! bind (Identity x) (\x -> (bind (f x) g))
  *** QED
