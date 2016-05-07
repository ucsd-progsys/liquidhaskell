
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

data L a = N |  C a (L a)

instance Eq a => Eq (L a) where
  N == N                 = True
  (C x xs) == (C x' xs') = x == x' && xs == xs'

{-@ axiomatize append @-}

$(axiomatize
  [d| append :: L a -> L a -> L a
      append N xs        = xs
      append (C y ys) xs = C y (append ys xs)
    |])



{-
axiom_append_N :: xs: L a -> {v:Proof  |  append N xs == xs }
axiom_append_N xs = Proof  

axiom_append_C :: xs: L a -> y:a > ys: L a 
                -> {v:Proof  |  append (C y ys) xs == C y (append ys xs) }
axiom_append_C xs y ys  = Proof 
-}



-- | Proof 1: N is neutral element


-- | axiomatixation of append will not be a haskell function anymore,
-- | thus the user cannot directly access it.
-- | use a function called `use_axiom` to apply these axioms.

-- prop_app_nil :: Eq a => L a -> Proof

{-@ prop_app_nil :: ys:L a -> {v:Proof | append ys N == ys} @-}
prop_app_nil :: (Eq a) => L a -> Proof
prop_app_nil N        = axiom_append_N N
prop_app_nil (C x xs)
    = 
                                      -- (C x xs) ++ N
           (axiom_append_C N x xs)
                                      -- == C x (xs ++ N)
      `by` (prop_app_nil xs)
                                      -- == C x xs




-- | Proof 2: append is associative

{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {v:Proof | append (append xs ys) zs == append xs (append ys zs) } @-}

prop_assoc :: Eq a => L a -> L a -> L a -> Proof

prop_assoc N ys zs  = auto 2 (append (append N ys) zs == append N (append ys zs))
-- =    refl (append (append N ys) zs) 
--           axiom_append_N ys             -- == append ys zs
--      `by` axiom_append_N (append ys zs) -- == append N (append ys zs)


prop_assoc (C x xs) ys zs
    = auto 2 (append (append (C x xs) ys) zs == append (C x xs) (append ys zs))
--      = refl e1
--        `by` pr1 `by` pr2 `by` pr3 `by` pr4
  where
    e1  = append (append (C x xs) ys) zs
    pr1 = axiom_append_C ys x xs
    e2  = append (C x (append xs ys)) zs
    pr2 = axiom_append_C zs x (append xs ys)
    e3  = C x (append (append xs ys) zs)
    pr3 = prop_assoc xs ys zs
    e4  = C x (append xs (append ys zs))
    pr4 = axiom_append_C (append ys zs) x xs
    e5  = append (C x xs) (append ys zs)


{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen :: L a -> Int
llen N = 0
llen (C x xs) = 1 + llen xs
