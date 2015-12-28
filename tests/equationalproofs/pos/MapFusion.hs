
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
      map f (C x xs) = f x `C` map f xs 
    |])

-- axioms: 
-- axiom_map_N :: forall f. map f N == N
-- axiom_map_C :: forall f x xs. map f (C x xs) == C (f x) (map f xs) 

{-@ axiomatize compose @-}

$(axiomatize
  [d| compose :: (b -> c) ->(a -> b) -> (a -> c)
      compose f g x = f (g x) 
    |])

{-@ prop_fusion :: f:(a -> a) -> g:(a -> a) -> xs:L a
                -> {v:Proof | map f (map g xs) ==  map (compose f g) xs }  @-}
prop_fusion     :: Eq a => (a -> a) -> (a -> a) -> L a -> Proof

prop_fusion f g N = 
--   refl e1 `by` pr1 `by` pr2 `by` pr3
    auto 2 (map f (map g N)  ==  map (compose f g) N)
{-
  where
    e1  = map f (map g N)
    pr1 = axiom_map_N g
    e2  = map f N
    pr2 = axiom_map_N f
    e3  = N
    pr3 = axiom_map_N (compose f g)
    e4  = map (compose f g) N
-}

prop_fusion f g (C x xs) = 
   auto 2 (map f (map g (C x xs)) == map (compose f g) (C x xs))
--    refl e1 `by` pr1 `by` pr2 `by` pr3 `by` pr4 `by` pr5
{-
  where
    e1 = map f (map g (C x xs))
    pr1 = axiom_map_C g x xs
    e2 = map f (C (g x) (map g xs))
    pr2 = axiom_map_C f (g x) (map g xs)
    e3 = C (f (g x)) (map f (map g xs))
    pr3 = prop_fusion f g xs
    e4 = C (f (g x)) (map (compose f g) xs)
    pr4 = axiom_compose f g x
    e5 = C ((compose f g) x) (map (compose f g) xs)
    pr5 = axiom_map_C (compose f g) x xs
    e6 = map (compose f g) (C x xs)
-}

{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen          :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs