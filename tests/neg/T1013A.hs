{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}
{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--no-adt"      @-} -- TODO: embed HKTs in SMTLIB2 ADTs (e.g. `Rec`)

{-# LANGUAGE RankNTypes #-}

module Bug where

import Prelude hiding (fmap)

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize _compose @-}
_compose :: (b -> c) -> (a -> b) -> a -> c
_compose f g x = f (g x)
{-# INLINE _compose #-}

{-@ data Rec1 f p = Rec1 { unRec1 :: f p } @-}
data Rec1 f p = Rec1 { unRec1 :: f p }

{-@
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapCompose :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:m a
                -> { fmap (_compose f g) x == _compose (fmap f) (fmap g) x }
  }
@-}
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapCompose :: forall a b c. (b -> c) -> (a -> b) -> m a -> Proof
  }

{-@ axiomatize fmapRec1 @-}
fmapRec1 :: (forall a b. (a -> b) -> f a -> f b)
         -> (p -> q) -> Rec1 f p -> Rec1 f q
fmapRec1 fmapF f (Rec1 fp) = Rec1 (fmapF f fp)

{-@ fmapRec1Compose :: fmapF:(forall a b. (a -> b) -> f a -> f b)
                    -> fmapFId:(forall a b c. f':(b -> c) -> g':(a -> b) -> y:(f a) -> { fmapF (_compose f' g') y == _compose (fmapF f') (fmapF g') y })
                    -> f:(q -> r)
                    -> g:(p -> q)
                    -> x:Rec1 f p
                    -> { fmapRec1 fmapF (_compose f g) x == _compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) x }
@-}
fmapRec1Compose :: (forall a b. (a -> b) -> f a -> f b)
                -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
                -> (q -> r) -> (p -> q) -> Rec1 f p -> Proof
fmapRec1Compose fmapF fmapFCompose f g r@(Rec1 fp)
  =   fmapRec1 fmapF (_compose f g) r
  ==. fmapRec1 fmapF (_compose f g) (Rec1 fp)
  ==. Rec1 (fmapF (_compose f g) fp)
  ==. Rec1 (_compose (fmapF f) (fmapF g) fp) ? fmapFCompose f g fp
  ==. Rec1 (fmapF f (fmapF g fp))
  ==. fmapRec1 fmapF f (Rec1 (fmapF g fp))
  ==. fmapRec1 fmapF f (fmapRec1 fmapF g (Rec1 fp))
  ==. _compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) (Rec1 fp)
  ==. _compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) r
  *** QED

vfunctorRec1 :: VerifiedFunctor f -> VerifiedFunctor (Rec1 f)
vfunctorRec1 (VerifiedFunctor fmapF fmapFCompose)
  = VerifiedFunctor (fmapRec1        fmapF)
                    (fmapRec1Compose fmapF fmapFCompose)
