{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Pretty
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Helpers for prettyprinting expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Pretty where

import Language.Stitch.LH.Op
import Language.Stitch.LH.Util
import Language.Stitch.LH.Data.Nat

import Text.PrettyPrint.ANSI.Leijen

lamPrec, appPrec, appLeftPrec, appRightPrec, ifPrec :: Prec
lamPrec = 1
appPrec = 9
appLeftPrec = 8.9
appRightPrec = 9
ifPrec = 1

opPrec, opLeftPrec, opRightPrec :: ArithOp -> Prec
opPrec      (precInfo -> (x, _, _)) = x
opLeftPrec  (precInfo -> (_, x, _)) = x
opRightPrec (precInfo -> (_, _, x)) = x

-- | Returns (overall, left, right) precedences for an 'ArithOp'
precInfo :: ArithOp -> (Prec, Prec, Prec)
precInfo Plus     = (5, 4.9, 5)
precInfo Minus    = (5, 4.9, 5)
precInfo Times    = (6, 5.9, 6)
precInfo Divide   = (6, 5.9, 6)
precInfo Mod      = (6, 5.9, 6)
precInfo Less     = (4, 4, 4)
precInfo LessE    = (4, 4, 4)
precInfo Greater  = (4, 4, 4)
precInfo GreaterE = (4, 4, 4)
precInfo Equals   = (4, 4, 4)

-- | A function that changes a 'Doc's color
type ApplyColor = Doc -> Doc

-- | The colors used for all rendered expressions
{-@ coloring :: { v : [ApplyColor] | len v > 0 } @-}
coloring :: [ApplyColor]
coloring = [red, green, yellow, blue, magenta, cyan]

{-@ ignore applyColor @-}
-- LH would need a proof that
-- @len (cycle coloring) > maxIndex v - scopedIndex v@
-- so @!!@ is safe to use.
applyColor :: ScopedVar -> ApplyColor
applyColor v = cycle coloring !! (maxIndex v - scopedIndex v)

{-@
data ScopedVar = ScopedVar
  { maxIndex    :: NumVarsInScope
  , scopedIndex :: { i : Nat | i < maxIndex }
  }
@-}
data ScopedVar = ScopedVar
  { maxIndex    :: NumVarsInScope
  , scopedIndex :: Nat
  }

-- The number of variables in scope.
{-@ type NumVarsInScope = Nat @-}
type NumVarsInScope = Nat
