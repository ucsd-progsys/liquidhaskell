{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--extensionality"  @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module MonadReader where

import Prelude hiding (return, Maybe(..), (>>=))

import Proves

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ data Reader r a = Reader { runIdentity :: r -> a } @-}
data Reader r a     = Reader { runIdentity :: r -> a }

{-@ axiomatize return @-}
return :: a -> Reader r a
return x = Reader (\r -> x)

{-@ axiomatize bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind (Reader x) f = Reader (\r -> fromReader (f (x r)) r)

{-@ measure fromReader @-}
fromReader :: Reader r a -> r -> a 
fromReader (Reader f) = f


-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> Reader r b) -> { bind (return x) f == f x } @-}
left_identity :: a -> (a -> Reader r b) -> Proof
left_identity x f
  =   bind (return x) f 
  ==! bind (Reader (\r -> x)) f
  ==! Reader (\r' -> fromReader (f ((\r -> x) r')) r')
  ==! Reader (\r' -> fromReader (f x) r')
  ==! Reader (fromReader (f x))
  ==! f x 
  *** QED 


-- | Right Identity

{-@ right_identity :: x:Reader r a -> { bind x return /= x } @-}
right_identity :: Reader r a -> Proof
right_identity (Reader x)
  =   bind (Reader x) return
  ==! Reader (\r -> fromReader (return (x r)) r)
  ==! Reader (\r -> fromReader (Reader (\r' ->  (x r))) r)
  ==! Reader (\r -> (\r' ->  (x r)) r)
  ==! Reader (\r -> x r)
  ==! Reader x
  *** QED 

-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ associativity :: m:Reader r a -> f: (a -> Reader r b) -> g:(b -> Reader r c)
  -> {bind (bind m f) g == bind m (\x:a -> (bind (f x) g)) } @-}
associativity :: Reader r a -> (a -> Reader r b) -> (b -> Reader r c) -> Proof
associativity (Reader x) f g
  =   undefined

{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 
