
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module ConcatMap where

import Axiomatize
import Equational 
import Prelude hiding (map, concatMap, concat)

data L a = N |  C a (L a)

instance Eq a => Eq (L a) where
  N == N                 = True
  (C x xs) == (C x' xs') = x == x' && xs == xs'

{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a 
      append N ys        = ys 
      append (C x xs) ys = C x (append xs ys)
    |])

{-@ axiomatize map @-}
$(axiomatize
  [d| map :: (a -> b) -> L a -> L b
      map f N        = N
      map f (C x xs) = f x `C` map f xs 
    |])

{-@ axiomatize concatMap @-}
$(axiomatize
  [d| concatMap :: (a -> L b) -> L a -> L b
      concatMap f N        = N 
      concatMap f (C x xs) = append (f x) (concatMap f xs)
    |])


{-@ axiomatize concatt @-}

$(axiomatize
  [d| concatt :: L (L a) -> L a 
      concatt N        = N 
      concatt (C x xs) = append x (concatt xs)
     |])


--   "concat/map" forall f xs . concat $ map f xs = concatMap f xs

{-@ prop_concatMap :: f:(a -> L (L a)) -> xs:L a
                   -> {v:Proof | (concatt (map f xs) == concatMap f xs) }  @-}

prop_concatMap :: Eq a => (a -> L (L a)) -> L a -> Proof  
prop_concatMap f N 
   = auto 1 (concatt (map f N) == concatMap f N)
{-   
--   = refl e1 `by` pr1 `by` pr2 `by` pr3 
  where
    e1  = concatt (map f N)
    pr1 = axiom_map_N f
    e2  = concatt N
    pr2 = axiom_concatt_N
    e3  = N
    pr3 = axiom_concatMap_N f 
    e4  = concatMap f N
-}

prop_concatMap f (C x xs) 
   = auto 2 (concatt (map f (C x xs)) == concatMap f (C x xs))
{-
  = refl e1 `by` pr1 `by` pr2 `by` pr3 `by` pr4 
  where 
    e1  = concatt (map f (C x xs)) 
    pr1 = axiom_concatt_C (f x) (map f xs)
    pr2 = axiom_concatMap_C f x xs 
    pr3 = axiom_map_C f x xs 
    pr4 = prop_concatMap f xs  
-}

{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen          :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs