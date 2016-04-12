
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

-- | Left identity: return a >>= f ≡ f a

{-@ prop_left_identity :: x:a -> f:(a -> Maybe a) -> {v:Proof | bind (return x) f == f x} @-}
prop_left_identity :: Eq a => a -> (a -> Maybe a) -> Proof
prop_left_identity x  f = rewrite 3 (bind (return x) f == f x)

{- 
prop_left_identity x  f = pr1 `by` pr2 
  where
    e1  = bind (return x) f 
    pr1 = axiom_return x 
    e2  = bind (Just x) f 
    pr2 = axiom_bind_Just f x 
    e3  = f x   
-}


-- | Right Identity m >>= return ≡  m
{-@ prop_right_identity :: m:Maybe a -> {v:Proof | bind m return == m } @-}
prop_right_identity :: Eq a => Maybe a -> Proof
prop_right_identity Nothing  = rewrite 0 (bind Nothing  return == Nothing) 
prop_right_identity (Just x) = rewrite 0 (bind (Just x) return == Just x)  

{- 
prop_right_identity Nothing = pr1 
  where
    e1  = bind Nothing return
    pr1 = axiom_bind_Nothing return
    e2  = Nothing

prop_right_identity (Just x) = pr1 `by` pr2 
  where
    e1  = bind (Just x) return 
    pr1 = axiom_bind_Just return x 
    e2  = return x 
    pr2 = axiom_return x 
    e3  = Just x 
-}


-- | Left Associativity: (m >>= f) >>= g ≡  m >>= (\x -> f x >>= g)

prop_left_associativity :: Eq a => Maybe a -> (a -> Maybe a) -> (a -> Maybe a) -> Proof 
prop_left_associativity m f g = Proof



