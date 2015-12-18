
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

-- |   A first example in equalional reasoning.
-- |  From the definition of append we should be able to
-- |  semi-automatically prove the two axioms.

-- | Note for soundness we need
-- | totallity: all the cases should be covered
-- | termination: we cannot have diverging things into proofs

{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Prelude hiding (map)

data L a = N |  C a (L a)

instance Eq a => Eq (L a) where
  N == N                 = True
  (C x xs) == (C x' xs') = x == x' && xs == xs'

{-@ axiomatize map @-}


$(axiomatize
  [d| map :: (a -> b) -> L a -> L b
      map f N        = N
      map f (C x xs) = C (f x) (map f xs)
    |])

-- axioms: 
-- axiom_map_N :: forall f. map f N == N
-- axiom_map_C :: forall f x xs. map f (C x xs) == C (f x) (map f xs) 

{-@ axiomatize compose @-}

$(axiomatize
  [d| compose :: (b -> c) ->(a -> b) -> (a -> c)
      compose f g x = f (g x) 
    |])


-- axiom_compose :: forall f g x. 

















