{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Blank where

data Some :: * -> * where
  SomeBool  :: Bool -> Some Int
  SomeInt   :: Int  -> Some Int

{-@ measure isBool @-}
isBool :: Some Int -> Bool
isBool (SomeBool  _) = True
isBool (SomeInt   _) = False

{-@ type SomeBool = { v: Some Int | isBool v } @-}

{-@ a :: SomeBool @-}
a = SomeBool True

{-@ b :: SomeBool @-}
b = SomeInt 5