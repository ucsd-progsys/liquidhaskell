
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

-- |   A first example in equalional reasoning.
-- |  From the definition of append we should be able to
-- |  semi-automatically prove the two axioms.

-- | Note for soundness we need
-- | totallity: all the cases should be covered
-- | termination: we cannot have diverging things into proofs

{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational


data L a = N |  C a (L a)

instance Eq a => Eq (L a) where



{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a
      append N xs        = xs
      append (C y ys) xs = C y (append ys xs)
    |])


-- | Proof 1: N is neutral element

{-@ prop_nil :: xs:L a -> {v:Proof | append xs N == xs } @-}
prop_nil     :: Eq a => L a -> Proof
prop_nil N
  =  axiom_append_N N

prop_nil (C x xs) = toProof e1 $ ((
  e1 === e2) pr1
     === e3) pr2
   where
   	e1  = append (C x xs) N
   	pr1 = axiom_append_C N x xs
   	e2  = C x (append xs N)
   	pr2 = prop_nil xs
   	e3  = C x xs

-- | axiomatixation of append will not be a haskell function anymore,
-- | thus the user cannot directly access it.
-- | use a function called `use_axiom` to apply these axioms.

-- prop_app_nil :: Eq a => L a -> Proof
{-@ prop_app_nil :: ys:L a -> {v:Proof | append ys N == ys} @-}
prop_app_nil N        =  auto (append N N        == N     ) -- axiom_append_N N
prop_app_nil (C x xs) =  auto (append (C x xs) N == C x xs)
{-
prop_app_nil (C x xs)
  = refl (append (C x xs) N)
                                      -- (C x xs) ++ N
      `by` (axiom_append_C N x xs)
                                      -- == C x (xs ++ N)
      `by` (prop_app_nil xs)
-}                                      -- == C x xs

-- | Proof 2: append is associative

{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {v:Proof | append (append xs ys) zs == append (append  xs ys) zs } @-}
prop_assoc :: Eq a => L a -> L a -> L a -> Proof

prop_assoc N ys zs =
  refl (append (append N ys) zs)
  `by` axiom_append_N ys             -- == append ys zs
  `by` axiom_append_N (append ys zs) -- == append N (append ys zs)

prop_assoc (C x xs) ys zs =
  refl e1
    `by` pr1 `by` pr2 `by` pr3 `by` pr4
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
