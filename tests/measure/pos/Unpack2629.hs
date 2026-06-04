{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--reflection" @-}

-- | This module tests that types that use UNPACK pragmas do not
-- prevent verification of the module if they are not used
-- in any functions or measures in the module.
module Unpack2629 where
data Crash = SomeInt {-# UNPACK #-}!Int

