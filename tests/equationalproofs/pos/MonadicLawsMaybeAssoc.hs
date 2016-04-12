
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational
import Prelude hiding (Monad(..), Maybe (..))


data Maybe a = Nothing | Just a deriving (Eq)

-- | Definition of the list monad

{-@ axiomatize return @-}
$(axiomatize
  [d| return :: a -> Maybe a
      return x = Just x 
    |])

{-@ axiomatize bind @-}
$(axiomatize
  [d| bind :: Maybe a -> (a -> Maybe b) -> Maybe b
      bind Nothing  f = Nothing
      bind (Just x) f = f x 
    |])


-- HERE 

-- | Left Associativity: (m >>= f) >>= g ≡  m >>= (\x -> f x >>= g)

{- prop_left_associativity :: m:Maybe a -> f:(a -> Maybe a) -> g:(a -> Maybe a) 
                            -> {v: Proof |  bind (bind m f) g == bind m (\x:a -> (bind (f x) g ))} @-}
prop_left_associativity :: Eq a => Maybe a -> (a -> Maybe a) -> (a -> Maybe a) ->  Proof 
prop_left_associativity Nothing f g = pr1 `by` pr2 `by` pr3 
  where
  	h   =  \x -> (bind (f x) g)
  	e1  = bind (bind Nothing f) g 
  	pr1 = axiom_bind_Nothing f
  	e2  = bind Nothing g 
  	pr2 = axiom_bind_Nothing g 
  	e3  = Nothing 
  	pr3 = axiom_bind_Nothing h 
  	e4  = bind Nothing h 

{- prop_left_associativity :: m:Maybe a -> f:(a -> Maybe a) -> g:(a -> Maybe a) 
                            -> {v: Proof |  bind (bind m f) g == bind m (\x:a -> (bind (f x) g ))} @-}
prop_left_associativity (Just x) f g = undefined --  bind (bind m f) g == bind m (\x -> (bind (f x) g ))



