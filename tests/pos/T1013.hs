{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}

{-# LANGUAGE RankNTypes #-}
module Generics2 where

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize _identity @-}
_identity :: a -> a
_identity x = x
{-# INLINE _identity #-}

{-@ data Rec1 f p = Rec1 { unRec1 :: f p } @-}
data Rec1 f p = Rec1 { unRec1 :: f p }

{-@ axiomatize fmapRec1 @-}
fmapRec1 :: (forall a b. (a -> b) -> f a -> f b)
         -> (p -> q) -> Rec1 f p -> Rec1 f q
fmapRec1 fmapF f (Rec1 fp) = Rec1 (fmapF f fp)

{-@ fmapRec1Id :: fmapF:(forall a b. (a -> b) -> f a -> f b)
               -> fmapFId:(forall a. y:(f a) -> { fmapF _identity y == y })
               -> r:Rec1 f p
               -> { fmapRec1 fmapF _identity r == r }
@-}
fmapRec1Id :: (forall a b. (a -> b) -> f a -> f b)
           -> (forall a. f a -> Proof)
           -> Rec1 f p -> Proof
fmapRec1Id fmapF fmapFId r@(Rec1 fp)
  =   fmapRec1 fmapF _identity r
  ==. Rec1 (fmapF _identity fp)
  ==. Rec1 (_identity fp) ? fmapFId fp
  ==. Rec1 fp
  ==. r
  *** QED