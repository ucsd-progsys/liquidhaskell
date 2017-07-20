{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}

module Fixme where

import Prelude hiding (map, concatMap)
import Language.Haskell.Liquid.ProofCombinators 

{-@ reflect append @-}
append :: L a -> L a -> L a
append Emp      ys = ys
append (x:::xs) ys = x ::: append xs ys

prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> {append xs Emp == xs}  @-}
prop_append_neutral Emp
  = append Emp Emp ==. Emp
  *** QED
prop_append_neutral (x ::: xs)
  = append (x ::: xs) Emp
  ==. x ::: (append xs Emp)
  ==. x ::: xs             ? prop_append_neutral xs
  *** QED

data L a = Emp | a ::: L a
{-@ data L [llen] a = Emp | (:::) { lHd ::a, lTl :: L a } @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs

