
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
import Equational 
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


{-
TODO 
 1. when sig is on it is crashing
 2. when auto is on it is crashing
 3. define the Cons case 

-}

{- prop_fusion :: f:(a -> a) -> g:(a -> a) -> xs:L a
                -> {v:Proof | map f (map g xs) ==  map (compose f g) xs }  @-}
prop_fusion     :: Eq a => (a -> a) -> (a -> a) -> L a -> Proof
prop_fusion f g N = 
--    auto 2 (map f (map g N) == map (compose f g) N)
   refl e1 `by` pr1 `by` pr2 `by` pr3
  where
    e1  = map f (map g N)
    pr1 = axiom_map_N g
    e2  = map f N
    pr2 = axiom_map_N f
    e3  = N
    fg  = compose f g
    pr3 = axiom_map_N (compose f g)
    e4  = map fg N

prop_fusion f g (C x xs) 
  = undefined  















