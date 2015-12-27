
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
      map f (C x xs) = f x `C` map f xs 
    |])


{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a 
      append N ys        = ys 
      append (C x xs) ys = C x (append xs ys)
    |])


--   "map/append" forall f xs ys. map f (xs ++ ys) = map f xs ++ map f ys
prop_map_append :: (a -> b) -> L a -> L a -> Prop 
prop_map_append f N ys = 
  auto 2 (map f (N `append` ys) == map f N `append` map f ys) 

{- Generated axioms: 
1. axiom_append_N (map f ys)
2. axiom_append_N ys 
3. axiom_map_N f 
-}  

prop_map_append f (C x xs) ys = 
  auto 3 (map f ((C x xs) `append` ys) == map f (C x xs) `append` map f ys) 


{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen          :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs