-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Unchecked
-- Copyright   :  (C) 2015 Richard Eisenberg
--                (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Defines the AST for un-type-checked expressions
--
----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{- LIQUID "--exact-data-cons" @-}

module Language.Stitch.LH.Unchecked where

import Language.Stitch.LH.Pretty
import Language.Stitch.LH.Type
import Language.Stitch.LH.Op
import Language.Stitch.LH.Util
import Language.Stitch.LH.Data.Nat as Nat

import Text.PrettyPrint.ANSI.Leijen

{-@
data UExp
  = UVar Nat
  | UGlobal String
  | ULam Ty UExp
  | UApp UExp UExp
  | ULet UExp UExp
  | UArith UExp ArithOp UExp
  | UCond UExp UExp UExp
  | UFix UExp
  | UIntE Int
  | UBoolE Bool
@-}

-- | Unchecked expression
data UExp
  = UVar Nat
  | UGlobal String
  | ULam Ty UExp
  | UApp UExp UExp
  | ULet UExp UExp
  | UArith UExp ArithOp UExp
  | UCond UExp UExp UExp
  | UFix UExp
  | UIntE Int
  | UBoolE Bool
  deriving (Eq, Show)

{-@
measure numFreeVars
numFreeVars :: UExp -> Nat
@-}
numFreeVars :: UExp -> Nat
numFreeVars (UVar v) = v + 1
numFreeVars (UGlobal _) = 0
numFreeVars (ULam _ body) = Nat.minus (numFreeVars body) 1
numFreeVars (UApp e1 e2) = Nat.max (numFreeVars e1) (numFreeVars e2)
numFreeVars (ULet e1 e2) =
    Nat.max (numFreeVars e1) (Nat.minus (numFreeVars e2) 1)
numFreeVars (UArith e1 _ e2) = Nat.max (numFreeVars e1) (numFreeVars e2)
numFreeVars (UCond e1 e2 e3) =
    Nat.max (Nat.max (numFreeVars e1) (numFreeVars e2)) (numFreeVars e3)
numFreeVars (UFix body) = numFreeVars body
numFreeVars (UIntE _) = 0
numFreeVars (UBoolE _) = 0

{-@
type VarsSmallerThan N = { e : UExp | numFreeVars e <= N }
type ClosedUExp = { e : UExp | numFreeVars e == 0 }
@-}

-- An expression paired with the bound for the valid
-- variable indices
{-@ data ScopedUExp = ScopedUExp (n :: NumVarsInScope) (VarsSmallerThan n) @-}
data ScopedUExp = ScopedUExp NumVarsInScope UExp
  deriving (Eq, Show)

instance Pretty ScopedUExp where
  pretty (ScopedUExp n e) = prettyExp n topPrec e

{-@ prettyExp :: n : NumVarsInScope -> Prec -> VarsSmallerThan n -> Doc @-}
prettyExp :: NumVarsInScope -> Prec -> UExp -> Doc
prettyExp n prec = \case
  UVar v       -> applyColor (ScopedVar n v) (char '#' <> int v)

  UGlobal name -> text name

  -- XXX: Putting the alternatives below in auxiliary functions would cause
  -- a mysterious failure in LH.
  ULam ty body -> maybeParens (prec >= lamPrec) $
    fillSep [ char 'λ' <> applyColor (ScopedVar (n + 1) 0) (char '#') <>
              text ":" <> pretty ty <> char '.'
            , prettyExp (n + 1) topPrec body ]

  UApp e1 e2 -> maybeParens (prec >= appPrec) $
    fillSep [ prettyExp n appLeftPrec  e1
            , prettyExp n appRightPrec e2 ]

  ULet e1 e2 -> maybeParens (prec >= lamPrec) $
    fillSep [ text "let" <+> applyColor (ScopedVar (n + 1) 0) (char '#') <+>
              char '=' <+> prettyExp n topPrec e1 <+> text "in"
            , prettyExp (n + 1) topPrec e2 ]

  UArith e1 op e2 -> maybeParens (prec >= opPrec op) $
    fillSep [ prettyExp n (opLeftPrec op) e1 <+> pretty op
            , prettyExp n (opRightPrec op) e2 ]

  UCond e1 e2 e3 -> maybeParens (prec >= ifPrec) $
    fillSep [ text "if" <+> prettyExp n topPrec e1
            , text "then" <+> prettyExp n topPrec e2
            , text "else" <+> prettyExp n topPrec e3 ]

  UFix body -> maybeParens (prec >= appPrec) $
                 text "fix" <+> prettyExp n topPrec body

  UIntE i -> int i

  UBoolE True -> text "true"

  UBoolE False -> text "false"
