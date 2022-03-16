{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Statement
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Defines the Stitch Statement type, which can either be a bare
-- expression or a global variable assignment.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Statement ( Statement(..) ) where

-- XXX: Import Op so LH doesn't fail with: Unknown type constructor `ArithOp`
import Language.Stitch.LH.Op
import Language.Stitch.LH.Unchecked

import Text.PrettyPrint.ANSI.Leijen

-- | A statement can either be a bare expression, which will be evaluated,
-- or an assignment to a global variable.
{-@
data Statement = BareExp ClosedUExp
               | NewGlobal String ClosedUExp
@-}
data Statement = BareExp UExp
               | NewGlobal String UExp
  deriving Show

instance Pretty Statement where
  pretty (BareExp e)     = pretty (ScopedUExp 0 e)
  pretty (NewGlobal v e) = text v <+> char '=' <+> pretty (ScopedUExp 0 e)
