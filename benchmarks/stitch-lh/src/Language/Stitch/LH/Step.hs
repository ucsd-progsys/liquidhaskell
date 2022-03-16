{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Step
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Stitch expression evaluators for checked expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Step where

-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Map as Map
-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators
import Language.Stitch.LH.Data.List (List(..))
-- XXX: Needed to avoid missing symbols in LH
import qualified Language.Stitch.LH.Data.List as List
import Language.Stitch.LH.Data.Nat
import Language.Stitch.LH.Check
import Language.Stitch.LH.Eval
import Language.Stitch.LH.Type


{-@
subst
  :: es:WellTypedExp Nil
  -> e0:WellTypedExp (Cons (exprType es) Nil)
  -> { er:WellTypedExp Nil | exprType e0 == exprType er }
@-}
subst :: Exp -> Exp -> Exp
subst es e0 =
    let ctx = Cons (exprType es) Nil
        er = substIndex ctx 0 es e0
     in er ? aClosedExpIsValidInAnyContext Nil ctx er

-- | Substitutes variables with a given index with a given expression.
--
-- XXX: The ctx argument is only needed to tell LH about preservation
-- of checkBindings, it is not needed at runtime.
{-@
substIndex
  :: ctx:List Ty
  -> i: { Nat | i = List.length ctx - 1 }
  -> es:{ WellTypedExp Nil | exprType es = List.elemAt i ctx }
  -> e0:WellTypedExp ctx
  -> { er:WellTypedExp ctx
     | numFreeVarsExp er <= i && exprType e0 == exprType er
     }
@-}
substIndex :: List Ty -> Nat -> Exp -> Exp -> Exp
substIndex ctx i es e0 = case e0 of
    Var _ v ->
      if v == i then
        es ? aClosedExpIsValidInAnyContext Nil ctx es
      else
        e0
    Lam ty e1 -> Lam ty (substIndex (Cons ty ctx) (i + 1) es e1)
    App e1 e2 -> App (substIndex ctx i es e1) (substIndex ctx i es e2)
    Arith e1 op e2 -> Arith (substIndex ctx i es e1) op (substIndex ctx i es e2)
    Let e1 e2 -> Let (substIndex ctx i es e1) (substIndex (Cons (exprType e1) ctx) (i + 1) es e2)
    Cond e1 e2 e3 -> Cond (substIndex ctx i es e1) (substIndex ctx i es e2) (substIndex ctx i es e3)
    Fix e1 -> Fix (substIndex ctx i es e1)
    IntE _ -> e0
    BoolE _ -> e0

{-@
step :: e:WellTypedExp Nil -> Maybe ({ r:WellTypedExp Nil | exprType e = exprType r })
@-}
step :: Exp -> Maybe Exp
step e0 = case e0 of
    Lam{} -> Nothing
    App e1 e2 -> case step e1 of
      Just e1' -> Just (App e1' e2)
      Nothing -> case step e2 of
        Just e2' -> Just (App e1 e2')
        Nothing -> case e1 of
          Lam _ e11 -> Just (subst e2 e11)
          _ -> Nothing -- This case is impossible but would need a prove
                       -- to verify it
    Let e1 e2 -> case step e1 of
      Just e1' -> Just (Let e1' e2)
      Nothing -> Just (subst e1 e2)
    Arith e1 op e2 -> case step e1 of
      Just e1' -> Just (Arith e1' op e2)
      Nothing -> case step e2 of
        Just e2' -> Just (Arith e1 op e2')
        Nothing -> Just (valueToExp (eval e0))
    Cond e1 e2 e3 -> case step e1 of
      Just e1' -> Just (Cond e1' e2 e3)
      Nothing -> case eval e1 of
        VBool True -> Just e2
        VBool False -> Just e3
    Fix e1 -> case step e1 of
      Just e1' -> Just (Fix e1')
      Nothing -> case e1 of
        Lam _ e11 -> Just (subst e0 e11)
        _ -> Nothing -- This case is impossible
    IntE{} -> Nothing
    BoolE{} -> Nothing

{-@
valueToExp
  :: v: {Value | valueType v = TInt || valueType v = TBool }
  -> { e:WellTypedExp Nil | exprType e = valueType v }
@-}
valueToExp :: Value -> Exp
valueToExp (VBool b) = BoolE b
valueToExp (VInt b) = IntE b
