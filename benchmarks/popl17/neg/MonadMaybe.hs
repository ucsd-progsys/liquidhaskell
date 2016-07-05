{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module MonadMaybe where

import Prelude hiding (return, Maybe(..))

import Proves
import Helper

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ axiomatize return @-}
return :: a -> Maybe a
return x = Just x

{-@ axiomatize bind @-}
bind :: Maybe a -> (a -> Maybe b) -> Maybe b
bind m f
  | is_Just m  = f (from_Just m)
  | otherwise  = Nothing

-- | Left Identity

{-@ left_identity :: x:a -> f:(a -> Maybe b) -> {v:Proof | bind (return x) f /= f x } @-}
left_identity :: a -> (a -> Maybe b) -> Proof
left_identity x f
  = toProof $
       bind (return x) f
         ==. bind (Just x) f
         ==. f (from_Just (Just x))
         ==. f x



-- | Right Identity

{-@ right_identity :: x:Maybe a -> {v:Proof | bind x return /= x } @-}
right_identity :: Maybe a -> Proof
right_identity Nothing
  = toProof $
      bind Nothing return
        ==. Nothing

right_identity (Just x)
  = toProof $
       bind (Just x) return
        ==. return x
        ==. Just x


-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)
{-@ associativity :: m:Maybe a -> f: (a -> Maybe b) -> g:(b -> Maybe c)
  -> {v:Proof | bind (bind m f) g /= bind m (\x:a -> (bind (f x) g))} @-}
associativity :: Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Proof
associativity Nothing f g
  = toProof $
       bind (bind Nothing f) g
         ==. bind Nothing g
         ==. Nothing
         ==. bind Nothing (\x -> bind (f x) g)
associativity (Just x) f g
  = toProof $
       bind (bind (Just x) f) g
         ==. bind (f x) g
         ==. (\x -> bind (f x) g) x
         ==. bind (Just x) (\x -> bind (f x) g)



data Maybe a = Nothing | Just a

{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:{Maybe a | is_Just xs } -> a @-}
from_Just (Just x) = x


{-@ measure is_Just @-}
is_Just :: Maybe a -> Bool
is_Just (Just _) = True
is_Just _        = False
