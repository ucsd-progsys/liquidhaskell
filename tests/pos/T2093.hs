{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-@ embed GHC.Natural.Natural as int @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
{-@ LIQUID "--no-totality" @-}

module T2093 where 
    
import Prelude 
import GHC.TypeLits
import GHC.Natural

newtype Unsigned (n :: Nat) = U Natural
instance KnownNat n => Num (Unsigned n)
  
instance Ord (Unsigned n)
instance Eq (Unsigned n)

type Hex = Unsigned 4
{-@ type Digit = {v : Hex | v <= 9 } @-}

{-@ x :: Digit @-}
x :: Hex
x = 3