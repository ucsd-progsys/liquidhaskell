
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


-- | Left Associativity: (m >>= f) >>= g ≡  m >>= (\x -> f x >>= g)

{-@ prop_left_associativity :: m:Maybe a -> f:(a -> Maybe a) -> g:(a -> Maybe a) 
                            -> {v: Bool | m == bind m (\x:a -> m ) } @-}
prop_left_associativity :: Eq a => Maybe a -> (a -> Maybe a) -> (a -> Maybe a) ->  Bool 
prop_left_associativity m f g = bind (bind m f) g == bind m (\x -> (bind (f x) g ))



