{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.String_LHAssumptions where

import Data.String
import GHC.Types_LHAssumptions()

{-@
measure stringlen :: a -> GHC.Types.Int

assume GHC.Internal.Data.String.fromString
    ::  forall a. GHC.Internal.Data.String.IsString a
    =>  i : [GHC.Types.Char]
    ->  { o : a | i ~~ o && len i == stringlen o }
@-}
