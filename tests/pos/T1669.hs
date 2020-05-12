{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--no-totality" @-}

module A where
import           Prelude                 hiding ( Semigroup
                                                , mappend
                                                )

data PNat = Z | S PNat

{-@ data Semigroup a = CSemigroup {mappend :: a -> a -> a} @-}
data Semigroup a = CSemigroup {mappend :: a -> a -> a}

{-@ reflect cmappend  @-}
cmappend :: PNat -> PNat -> PNat
cmappend Z     n = n
cmappend (S m) n = S (cmappend m n)

{-@ reflect semigroupPNat  @-}
semigroupPNat :: Semigroup PNat
semigroupPNat = CSemigroup cmappend


{-@ ple clawAssociative @-}
{-@ clawAssociative :: v:PNat -> v':PNat -> v'':PNat  
  -> { mappend semigroupPNat (mappend semigroupPNat v v') v'' == mappend semigroupPNat v (mappend semigroupPNat v' v'')}@-}
clawAssociative :: PNat -> PNat -> PNat -> ()
clawAssociative Z     _ _ = ()
-- clawAssociative (S p) m n = clawAssociative p m n
