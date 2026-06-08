{-@ LIQUID "" @-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Test that a data type named 'TT' does not panic, even though there is an
-- imported type alias 'TT' in GHC.Types_LHAssumptions.
-- The type alias should still take precedence when 'TT' appears in a type
-- position.
module T2446 where

{-@ data TT = T @-}
data TT = T
