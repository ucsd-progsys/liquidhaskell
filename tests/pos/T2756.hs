{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
-- | Tests that we can check multiple family instances as long as they
-- have the same arity.
module T2756 where

data Checked_
data Unchecked_

class Checking check where
   data Result check a
   switchCheck :: f Checked_ -> f Unchecked_ -> f check

data CheckSingleton check where
   Checked :: CheckSingleton Checked_
   Unchecked :: CheckSingleton Unchecked_


-- LiquidHaskell-9.14 fails on this one:
instance Checking Checked_ where
   newtype Result Checked_ a = CheckedResult {getChecked :: Either String a}
   switchCheck f _ = f

instance Checking Unchecked_ where
   newtype Result Unchecked_ a = UncheckedResult {getUnchecked :: a}
   switchCheck _ f = f

