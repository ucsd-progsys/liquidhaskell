{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc"     @-}

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes     #-}
module Iso where

import Language.Haskell.Liquid.ProofCombinators

{-@ data Iso a b = Iso { to   :: a -> b
                       , from :: b -> a
                       , tof  :: y:b -> { to (from y) == y }
                       , fot  :: x:a -> { from (to x) == x }
                       }
@-}

data Iso a b = Iso { to   :: a -> b
                   , from :: b -> a
                   , tof  :: b -> Proof
                   , fot  :: a -> Proof
                   }

{-@ axiomatize identity @-}
identity :: a -> a
identity x = x
{-# INLINE identity #-}

-- | The identity 'Iso'.
isoRefl :: Iso a a
isoRefl = Iso identity
              identity
              (\x -> identity (identity x) ==. x *** QED)
              (\x -> identity (identity x) ==. x *** QED)

-- | 'Iso's are symmetric.
isoSym :: Iso a b -> Iso b a
isoSym Iso { to, from, tof, fot } = Iso from to fot tof
