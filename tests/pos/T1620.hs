{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Semigroup where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                )
{-@ data Monoid a = CMonoid {
  mappend :: a -> a,
  mempty :: a }
 @-}

data Monoid a = CMonoid {
  mappend :: a -> a,
  mempty :: a
  }

{-@ data VMonoid a = CVMonoid {
   p1VMonoid :: Monoid a
  , lawEmpty :: x:a -> {mappend p1VMonoid  x == mempty p1VMonoid}
  } @-}

data VMonoid a = CVMonoid {
  p1VMonoid :: Monoid a
  , lawEmpty :: a -> ()

  }
data Id a = Id {getId :: a}

{-@ reflect cmappend @-}
cmappend :: Monoid a -> Id a -> Id a
cmappend d (Id x) = Id (mappend d x)

{-@ reflect fMonoidId @-}
fMonoidId :: Monoid a -> Monoid (Id a)
fMonoidId d = CMonoid (cmappend d) (Id (mempty d))

{-@ reflect fMonoidId' @-}
fMonoidId' :: Monoid a -> Monoid (Id a)
fMonoidId' d = fMonoidId d



{-@ clawEmpty :: d:(VMonoid a) -> (x:(Id a) -> { mappend (fMonoidId' ((p1VMonoid d))) x == (mempty (fMonoidId' (p1VMonoid d)))}) @-}
{-@ reflect clawEmpty @-}
clawEmpty :: VMonoid a -> Id a -> ()
clawEmpty d (Id v) = lawEmpty d v


-- does not check using clawEmpty
fVMonoidId :: VMonoid a -> VMonoid (Id a)
fVMonoidId d = CVMonoid (fMonoidId (p1VMonoid d)) (clawEmpty d)
