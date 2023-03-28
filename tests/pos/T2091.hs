{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module T2091 where 
    
import Prelude (Bool(..))
import GHC.TypeLits

data Vec (n :: Nat) a where
    VCons :: a -> Vec n a -> Vec (1 + n) a
    VNil :: Vec 0 a

{-@ ys0 :: Vec _ Bool @-}
ys0 :: Vec 0 Bool
ys0 = VNil

type Vec1 = Vec 1 
{-@ type T = {v:Bool | v } @-}
{-@ ys1 :: Vec _ T @-}
ys1 :: Vec 1 Bool
ys1 = VCons True VNil
