{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.String_LHAssumptions where

import Data.String
import GHC.Types_LHAssumptions()

{-@
measure stringlen :: a -> Int

assume fromString
    ::  forall a. IsString a
    =>  i : [Char]
    ->  { o : a | i ~~ o && len i == stringlen o }
@-}
