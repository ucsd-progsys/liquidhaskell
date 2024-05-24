{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-@ LIQUID "--no-exact-data-cons" @-}
module GHC.Maybe_LHAssumptions where

{-@
data Maybe a = Nothing | Just a
@-}
