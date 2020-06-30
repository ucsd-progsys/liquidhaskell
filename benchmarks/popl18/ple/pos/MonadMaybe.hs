{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--ple"               @-}
{- LIQUID "--betaequivalence"   @-}

module MonadMaybe where

import Prelude hiding (return)

import Language.Haskell.Liquid.ProofCombinators

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ reflect return @-}
return :: a -> Maybe a
return x = Just x

{-@ reflect bind @-}
bind :: Maybe a -> (a -> Maybe b) -> Maybe b
bind m f
  | is_Just m  = f (from_Just m)
  | otherwise  = Nothing

-- | Left Identity

{-@ left_identity :: x:a -> f:(a -> Maybe b) -> {v:Proof | bind (return x) f == f x } @-}
left_identity :: a -> (a -> Maybe b) -> Proof
left_identity x f
  = trivial 



-- | Right Identity

{-@ right_identity :: x:Maybe a -> {v:Proof | bind x return == x } @-}
right_identity :: Maybe a -> Proof
right_identity Nothing
  = trivial 
right_identity (Just x)
  = trivial 


-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)
{-@ assume associativity :: m:Maybe a -> f: (a -> Maybe b) -> g:(b -> Maybe c)
      -> {v:Proof | bind (bind m f) g == bind m (\x:a -> (bind (f x) g))} @-}
associativity :: Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Proof
associativity Nothing f g
  =   trivial 
associativity (Just x) f g
  =   trivial 

{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:{Maybe a | is_Just xs } -> a @-}
from_Just (Just x) = x


{-@ measure is_Just @-}
is_Just :: Maybe a -> Bool
is_Just (Just _) = True
is_Just _        = False
