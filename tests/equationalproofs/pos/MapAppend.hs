
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

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


{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a 
      append N ys        = ys 
      append (C x xs) ys = C x (append xs ys)
    |])



--   "map/append" forall f xs ys. map f (xs ++ ys) = map f xs ++ map f ys
{-@ prop_map_append ::  f:(a -> a) -> xs:L a -> ys:L a 
                    -> {v:Proof | map f (append xs ys) == append (map f xs) (map f ys) }
  @-}
prop_map_append :: Eq a => (a -> a) -> L a -> L a -> Proof
-- prop_map_append f N ys = auto 2 (map f (N `append` ys) == map f N `append` map f ys) 
-- prop_map_append f N ys = auto 2 (map f (N `append` ys) == map f N `append` map f ys) 
prop_map_append f xs ys = cases 2 (map f (xs `append` ys) == map f xs `append` map f ys) 

{- Generated axioms: 
1. axiom_append_N (map f ys)
2. axiom_append_N ys 
3. axiom_map_N f 
-}  

{-  
prop_map_append f (C x xs) ys = 
  auto 2  (map f (append (C x xs) ys) == append (map f (C x xs)) (map f ys))
  -- refl (append (map f (C x xs)) (map f ys))
  --   `by` pr1 `by` pr2 `by` pr3 `by` pr4 `by` pr5 
    where
      e1  = append (map f (C x xs)) (map f ys)
      pr1 = axiom_map_C f x xs
      e2  = append (C (f x) (map f xs)) (map f ys)
      pr2 = axiom_append_C  (map f ys) (f x) (map f xs)
      e3  = C (f x) (append (map f xs) (map f ys))
      pr3 = prop_map_append f xs ys
      e4 = C (f x) (map f (append xs ys))
      pr4 = axiom_map_C f x (append xs ys)
      e5  = map f (C x (append xs ys))
      pr5 = axiom_append_C ys x xs
      e6  = map f (append (C x xs) ys)
-}


{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen          :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs