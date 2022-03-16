{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Op
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Defines arithmetic and logical operators
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Op (

  -- * Arithmetic operators
  ArithOp(..), arithType,

  ) where

import GHC.Generics
import Data.Hashable
import Language.Stitch.LH.Type
import Language.Stitch.LH.Util (render)

import Text.PrettyPrint.ANSI.Leijen

-- | An @ArithOp ty@ is an operator on numbers that produces a result
-- of type @ty@
data ArithOp
  = Plus
  | Minus
  | Times
  | Divide
  | Mod
  | Less
  | LessE
  | Greater
  | GreaterE
  | Equals
  deriving (Eq, Generic, Hashable)

-- | Extract the result type of an Op
{-@ measure arithType @-}
arithType :: ArithOp -> Ty
arithType Plus     = TInt
arithType Minus    = TInt
arithType Times    = TInt
arithType Divide   = TInt
arithType Mod      = TInt
arithType Less     = TBool
arithType LessE    = TBool
arithType Greater  = TBool
arithType GreaterE = TBool
arithType Equals   = TBool

{-@ invariant { op:ArithOp | arithType op = TBool || arithType op = TInt } @-}

-------------------------------------
-- Pretty-printing

instance Pretty ArithOp where
  pretty Plus     = char '+'
  pretty Minus    = char '-'
  pretty Times    = char '*'
  pretty Divide   = char '/'
  pretty Mod      = char '%'
  pretty Less     = char '<'
  pretty LessE    = text "<="
  pretty Greater  = char '>'
  pretty GreaterE = text ">="
  pretty Equals   = text "=="

instance Show ArithOp where
  show = render . pretty
