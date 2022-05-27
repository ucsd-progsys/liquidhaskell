{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--exact-data-con" @-}
{- LIQUID "--ple" @-}

module ExactGADT7 where

data Some a where
  SomeBool  :: Bool -> Some Bool
  SomeInt   :: Int  -> Some Int

{-@ measure isBool @-}
isBool :: Some a -> Bool
isBool (SomeBool  _) = True
isBool (SomeInt   _) = False

{-@ type Thing = { v: Some Bool | isBool v } @-}

{-@ a :: Thing @-}
a = SomeBool True

{-@ b :: Thing @-}
b = SomeBool True
