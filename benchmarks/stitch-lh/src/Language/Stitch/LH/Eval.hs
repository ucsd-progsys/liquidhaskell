{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-positivity-check" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Eval
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Stitch expression evaluators for checked expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Eval where

-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Map as Map
-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators (Proof, trivial, (?))
import Language.Stitch.LH.Data.List (List(..))
import qualified Language.Stitch.LH.Data.List as List
import Language.Stitch.LH.Data.Nat
import Language.Stitch.LH.Check
import Language.Stitch.LH.Op
import Language.Stitch.LH.Type

import Text.PrettyPrint.ANSI.Leijen

------------------------------------------------
-- Evaluation

-- CHALLENGE: The first parameter of VFun below should be a closed expression.
-- Change the Spec so it is closed and fix the program which is buggy.
--
-- This is visible when printing function that are partially
-- applied.
--
-- > λ> (\a:Int . \b:Int . a * b) 2
-- > λ#:Int. #1 * #0 : Int -> Int
--

{-@
type ValueT T = { v:Value | valueType v = T }
data Value
       = VInt Int
       | VBool Bool
       | VFun (vfun_e :: FunExp)
              (   { v:Value | funArgTy (exprType vfun_e) = valueType v }
               -> { vr:Value | funResTy (exprType vfun_e) = valueType vr }
              )
@-}
data Value = VInt Int | VBool Bool | VFun Exp (Value -> Value)

instance Pretty Value where
  pretty = \case
    VInt i -> int i
    VBool True -> text "true"
    VBool False -> text "false"
    VFun e _ -> pretty (ScopedExp (numFreeVarsExp e) e)

{-@
// XXX: Why can't we reflect map?
// XXX: If using measure, LH fails with: elaborate makeKnowledge failed on
reflect mapValueType
mapValueType
  :: vs:List Value
  -> { ts:List Ty
     | List.length ts = List.length vs
     }
@-}
mapValueType :: List Value -> List Ty
mapValueType Nil = Nil
mapValueType (Cons x xs) = Cons (valueType x) (mapValueType xs)

{-@ measure valueType @-}
valueType :: Value -> Ty
valueType VInt{} = TInt
valueType VBool{} = TBool
valueType (VFun e _) = exprType e

-- | Evaluate an expression, using big-step semantics.
{-@
eval
  :: e : WellTypedExp Nil
  -> { v:Value | valueType v = exprType e }
@-}
eval :: Exp -> Value
eval = evalWithCtx Nil

{-@
evalWithCtx :: ctx:List Value -> e:WellTypedExp (mapValueType ctx) -> ValueT (exprType e)
@-}
evalWithCtx :: List Value -> Exp -> Value
evalWithCtx ctx e0 = case e0 of
    Var _ i ->
      List.elemAt i (ctx ? mapValueType ctx) ? elemAtThroughMapValueType_prop i ctx

    Lam ty_arg e -> VFun e0 ((\v -> evalWithCtx (Cons v ctx) e) ? funResTy_lam_prop ty_arg e)

    App e1 e2 -> case evalWithCtx ctx e1 of
      VFun _ f -> f (evalWithCtx ctx e2)

    Let e1 e2 -> evalWithCtx (Cons (evalWithCtx ctx e1) ctx) e2

    Arith e1 op e2 -> evalArithOp op (evalWithCtx ctx e1) (evalWithCtx ctx e2)

    Cond e1 e2 e3 -> case evalWithCtx ctx e1 of
      VBool True -> evalWithCtx ctx e2
      VBool False -> evalWithCtx ctx e3

    Fix e -> case evalWithCtx ctx e of
      VFun _ f -> valueFix (exprType e0) f

    IntE i -> VInt i

    BoolE b -> VBool b

{-@
valueFix :: t:Ty -> (ValueT t -> ValueT t) -> ValueT t
lazy valueFix
@-}
valueFix :: Ty -> (Value -> Value) -> Value
valueFix t f = f (valueFix t f)

{-@
evalArithOp :: op:ArithOp -> ValueT TInt -> ValueT TInt -> ValueT (arithType op)
@-}
evalArithOp :: ArithOp -> Value -> Value -> Value
evalArithOp = \case
  Plus -> evalIntOp (+)
  Minus -> evalIntOp (-)
  Times -> evalIntOp (*)
  Divide -> evalIntOp unsafeDiv
  Mod -> evalIntOp unsafeMod
  Less -> evalBoolOp (<)
  LessE -> evalBoolOp (<=)
  Greater -> evalBoolOp (>)
  GreaterE -> evalBoolOp (>=)
  Equals -> evalBoolOp (==)

{-@
evalIntOp :: (Int -> Int -> Int) -> ValueT TInt -> ValueT TInt -> ValueT TInt
@-}
evalIntOp :: (Int -> Int -> Int) -> Value -> Value -> Value
evalIntOp f (VInt i0) (VInt i1) = VInt (f i0 i1)

{-@
evalBoolOp :: (Int -> Int -> Bool) -> ValueT TInt -> ValueT TInt -> ValueT TBool
@-}
evalBoolOp :: (Int -> Int -> Bool) -> Value -> Value -> Value
evalBoolOp f (VInt i0) (VInt i1) = VBool (f i0 i1)

{-@ ignore unsafeDiv @-}
unsafeDiv :: Int -> Int -> Int
unsafeDiv = div
{-@ ignore unsafeMod @-}
unsafeMod :: Int -> Int -> Int
unsafeMod = mod

{-@
elemAtThroughMapValueType_prop
  :: i:Nat
  -> ctx : { List Value | i < List.length ctx }
  -> { List.elemAt i (mapValueType ctx) = valueType (List.elemAt i ctx) }
@-}
elemAtThroughMapValueType_prop :: Nat -> List Value -> Proof
elemAtThroughMapValueType_prop 0 (Cons _ _) = trivial
elemAtThroughMapValueType_prop i (Cons _ ctxs) =
  elemAtThroughMapValueType_prop (i - 1) ctxs

{-@
// XXX: why is this proof necessary?
funResTy_lam_prop
  :: ty:Ty -> e:Exp -> { funResTy (exprType (Lam ty e)) = exprType e }
@-}
funResTy_lam_prop :: Ty -> Exp -> Proof
funResTy_lam_prop _ _ = trivial
