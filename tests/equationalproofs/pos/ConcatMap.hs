
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Append where

import Axiomatize
import Equational 
import Prelude hiding (map, concatMap, concat, append)

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


{-@ axiomatize concat @-}
$(axiomatize
  [d| concat :: L (L a) -> L a 
      concat N        = N 
      concat (C x xs) = append x (concat xs)
    |])


--   "concat/map" forall f xs . concat $ map f xs = concatMap f xs

prop_concatMap :: Eq a => (a -> L (L a)) -> L a -> Proof  
prop_concatMap f N 
  = auto 2 (concat (map f N) == concatMap f N)


prop_concatMap f (C x xs) 
  = auto 2 (concat (map f (C x xs)) == concatMap f (C x xs))

{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen          :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs