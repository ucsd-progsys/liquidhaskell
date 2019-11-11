{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--rankNTypes" @-}

{-# LANGUAGE RankNTypes          #-}

module T1546 where

import Language.Haskell.Liquid.Equational 

{-@ reflect first @-}
first :: (a -> b) -> (forall z. (a,z) -> (b,z))
first f (a, z) = (f a, z)

lemma :: (forall z. (a,z) -> (b,z)) -> (a,z) -> ()
{-@ lemma :: g:((a,z) -> (b,z)) -> x:(a,z) -> {v:() | g x == first (fOfG g) x } @-}
lemma g x
  =  g x ==. first (fOfG g) x *** QED

{-@ reflect fOfG @-}
fOfG :: (forall z. (a,z) -> (b,z)) -> a -> b
fOfG g x = case g (x, ()) of {(y,_) -> y}