{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Half where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, pred)

{-@ data Nats where
        Zero :: Nats
        Suc :: n:Nats -> Nats @-}
data Nats where
  Zero :: Nats
  Suc :: Nats -> Nats
  deriving (Eq)

{-@ reflect even @-}
{-@ even:: n:Nats -> Bool @-}
even :: Nats -> Bool
even Zero = True
even (Suc n) = not (even n)

{-@ reflect half @-}
{-@ half:: n:{n:Nats | even n} -> Nats @-}
half Zero = Zero
half (Suc Zero) = Zero
half (Suc (Suc n)) = Suc (half n)

{-@ surprise:: {half (Suc (Suc (Suc Zero))) == Suc Zero} @-}
surprise:: Proof
surprise = trivial
