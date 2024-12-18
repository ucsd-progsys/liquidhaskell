{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module Data.List_LHAssumptions where

-- TODO: For some reason, the specifications of GHC.List have
-- a role when verifying functions from Data.List. e.g
-- basic/pos/AssmReflFilter.hs
--
-- Needs to be investigated.
import GHC.List_LHAssumptions()
