{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Semigroup where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                )

{-@ data Semigroup a = CSemigroup {
   mappend :: a -> a -> a
   } @-}
data Semigroup a = CSemigroup {
   mappend :: a -> a -> a
   }

{-@ data VSemigroup a = CVSemigroup {
  p1VSemigroup :: Semigroup a, 
  lawAssociative :: v:a -> v':a -> v'':a -> {mappend p1VSemigroup (mappend p1VSemigroup v v') v'' == mappend p1VSemigroup v (mappend p1VSemigroup v' v'')}
  }  
@-}

data VSemigroup a = CVSemigroup {
  p1VSemigroup :: Semigroup a,
  lawAssociative :: a -> a -> a -> ()
  }

{-@ data Monoid a = CMonoid {
  p1Monoid :: Semigroup a,
  mempty :: a
                        }
 @-}

data Monoid a = CMonoid {
  p1Monoid :: Semigroup a,
  mempty :: a
                        }

{-@ data VMonoid a = CVMonoid {
   p1VMonoid :: VSemigroup a
  , p2VMonoid :: Monoid a
  , lawEmpty :: x:a -> {mappend (p1VSemigroup p1VMonoid) (mempty p2VMonoid) x == x && mappend (p1VSemigroup p1VMonoid) x (mempty p2VMonoid) == x}
  } @-}

data VMonoid a = CVMonoid {
  p1VMonoid :: VSemigroup a
  , p2VMonoid :: Monoid a
  , lawEmpty :: a -> ()

  }
data Dual a = Dual {getDual :: a}

{-@ reflect cmappend @-}
cmappend :: Semigroup a -> Dual a -> Dual a -> Dual a
cmappend d (Dual x) (Dual y) = Dual (mappend d y x)

{-@ inline fSemigroupDual @-}
fSemigroupDual :: Semigroup a -> Semigroup (Dual a)
fSemigroupDual d = CSemigroup (cmappend d)

{-@ inline cp1Monoid @-}
cp1Monoid :: Monoid a -> Semigroup (Dual a)
cp1Monoid d = fSemigroupDual (p1Monoid d)

{-@ reflect cmempty @-}
cmempty :: Monoid a -> Dual a
cmempty d = Dual (mempty d)

{-@ inline fMonoidDual @-}
fMonoidDual :: Monoid a -> Monoid (Dual a)
fMonoidDual d = CMonoid (cp1Monoid d) (cmempty d)

{-@ inline cp1VSemigroup @-}
cp1VSemigroup :: VSemigroup a -> Semigroup (Dual a)
cp1VSemigroup d = fSemigroupDual (p1VSemigroup d)

{-@ reflect clawAssociative @-}
{-@ clawAssociative :: d:VSemigroup a -> v:Dual a -> v':Dual a -> v'':Dual a -> { mappend (fSemigroupDual (p1VSemigroup d)) (mappend (fSemigroupDual (p1VSemigroup d)) v v') v'' == mappend (fSemigroupDual (p1VSemigroup d)) v (mappend (fSemigroupDual (p1VSemigroup d)) v' v'')} @-}
clawAssociative :: VSemigroup a -> Dual a -> Dual a -> Dual a -> ()
clawAssociative d (Dual v) (Dual v') (Dual v'') = lawAssociative d v'' v' v

{-@ inline fVSemigroupDual @-}
fVSemigroupDual :: VSemigroup a -> VSemigroup (Dual a)
fVSemigroupDual d = CVSemigroup (cp1VSemigroup d) (clawAssociative d)

{-@ inline cp1VMonoid @-}
{-@ cp1VMonoid :: d:VMonoid a -> VSemigroup (Dual a) @-}
cp1VMonoid :: VMonoid a -> VSemigroup (Dual a)
cp1VMonoid d = fVSemigroupDual (p1VMonoid d)

{-@ inline cp2VMonoid @-}
cp2VMonoid :: VMonoid a -> Monoid (Dual a)
cp2VMonoid d = fMonoidDual (p2VMonoid d)

{-@ clawEmpty :: d:(VMonoid a) -> x:(Dual a) -> { mappend (fSemigroupDual (p1VSemigroup (p1VMonoid d))) (mempty (fMonoidDual (p2VMonoid d))) x == x      && mappend (fSemigroupDual (p1VSemigroup (p1VMonoid d))) x (mempty (fMonoidDual (p2VMonoid d))) == x} @-}
{-@ reflect clawEmpty @-}
clawEmpty :: VMonoid a -> Dual a -> ()
clawEmpty d (Dual v) = lawEmpty d v

{-@ reflect k @-}
k :: a -> b -> b
k _ x = x
-- (mappend (cp1VMonoid ...) ... )
{-@ reflect fVMonoidDual @-}
fVMonoidDual :: VMonoid a -> VMonoid (Dual a)
fVMonoidDual d = CVMonoid (cp1VMonoid d) (cp2VMonoid d) (clawEmpty d)

{-@ trivial :: d:VMonoid a -> {fVMonoidDual d == CVMonoid (cp1VMonoid d) (cp2VMonoid d) (clawEmpty d)} @-}
trivial :: VMonoid a -> ()
trivial d = fVMonoidDual d `k` ()


