{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module MapFusion where

import Prelude hiding (map, concatMap)

import Proves


{-@ axiomatize append @-}
append :: L a -> L a -> L a
append Emp      ys = ys
append (x:::xs) ys = x ::: append xs ys

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f xs
  | llen xs == 0 = Emp
  | otherwise    = f (hd xs) ::: map f (tl xs)

{-@ axiomatize concatMap @-}
concatMap :: (a -> L b) -> L a -> L b
concatMap f xs
  | llen xs == 0 = Emp
  | otherwise    = append (f (hd xs)) (concatMap f (tl xs))


{-@ axiomatize concatt @-}
concatt :: L (L a) -> L a
concatt xs
  | llen xs == 0 = Emp
  | otherwise    = append (hd xs) (concatt (tl xs))


prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> {append xs Emp == xs}  @-}
prop_append_neutral Emp
  = append Emp Emp ==! Emp
  *** QED
prop_append_neutral (x ::: xs)
  = append (x ::: xs) Emp
  ==! x ::: (append xs Emp)
  ==! x ::: xs             ? prop_append_neutral xs
  *** QED

{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {append (append xs ys) zs == append xs (append ys zs) } @-}
prop_assoc :: L a -> L a -> L a -> Proof
prop_assoc Emp ys zs
  =   append (append Emp ys) zs
  ==! append ys zs
  ==! append Emp (append ys zs)
  *** QED

prop_assoc (x ::: xs) ys zs
  =   append (append (x ::: xs) ys) zs
  ==! append (x ::: append xs ys) zs
  ==! x ::: append (append xs ys) zs
  ==! x ::: append xs (append ys zs)  ? prop_assoc xs ys zs
  ==! append (x ::: xs) (append ys zs)
  *** QED



{-@ prop_map_append ::  f:(a -> a) -> xs:L a -> ys:L a
                    -> {map f (append xs ys) == append (map f xs) (map f ys) }
  @-}
prop_map_append :: (a -> a) -> L a -> L a -> Proof
prop_map_append f Emp ys
  =   map f (append Emp ys)
  ==! map f ys
  ==! append Emp (map f ys)
  ==! append (map f Emp) (map f ys)
  *** QED

prop_map_append f (x ::: xs) ys
  =   map f (append (x ::: xs) ys)
  ==! map f (x ::: append xs ys)
  ==! f x ::: map f (append xs ys)
  ==! f x ::: append (map f xs) (map f ys) ? prop_map_append f xs ys
  ==! append (f x ::: map f xs) (map f ys)
  ==! append (map f (x ::: xs)) (map f ys)
  *** QED


{-@ prop_concatMap :: f:(a -> L (L a)) -> xs:L a
                   -> { concatt (map f xs) == concatMap f xs }
  @-}

prop_concatMap :: (a -> L (L a)) -> L a -> Proof
prop_concatMap f Emp
  =   concatt (map f Emp)
  ==! concatt Emp
  ==! Emp
  ==! concatMap f Emp
  *** QED

prop_concatMap f (x ::: xs)
  =   concatt (map f (x ::: xs))
  ==! concatt (f x ::: map f xs)
  ==! append (f x) (concatt (map f xs))
  ==! append (f x) (concatMap f xs)     ? prop_concatMap f xs
  ==! concatMap f (x ::: xs)
  *** QED



data L a = Emp | a ::: L a
{-@ data L [llen] a = Emp | (:::) {x::a, xs :: L a } @-}


{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (x ::: _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (_ ::: xs) = xs
