module LambdaEval where

import Data.List        (lookup)

import LiquidPrelude    (assert)

{-# ANN module "spec   lambdaEval.hs.spec" #-}
{-# ANN module "hquals lambdaEval.hs.hquals" #-}


---------------------------------------------------------------------
----------------------- Datatype Definition -------------------------
---------------------------------------------------------------------

data Expr 
  = Const Int
  | Plus Expr Expr
  | Lam String Expr
  | Var String
  | App Expr Expr
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

-- A "value" is simply: {v: Expr | (? (isValue v)) } *)

eval sto (Const i) 
  = (sto, Const i)

eval sto (Var x)  
  = (sto, v) 
  where (Just v) = lookup x sto

eval sto (Plus e1 e2)
  = (sto, Const (i1 + i2))
  where (_, Const i1) = eval sto e1 
        (_, Const i2) = eval sto e2

eval sto (App e1 e2)
  = eval ((x, v2) : sto1) e
  where (sto1, (Lam x e)) = eval sto e1 
        (_   , v2)        = eval sto e2

eval sto (Lam x e) 
  = (sto, Lam x e)

eval sto (Pair e1 e2)
  = (sto, Pair v1 v2)
  where (_, v1) = eval sto e1
        (_, v2) = eval sto e2

eval sto (Fst e)
  = (sto, v1)
  where (sto, (Pair v1 _)) = eval sto e 

eval sto (Snd e)
  = (sto, v2)
  where (sto, (Pair _ v2)) = eval sto e 

---------------------------------------------------------------------
-------------------------- Value Checker ----------------------------
---------------------------------------------------------------------

check (Const _)    = True
check (Lam _ _)    = True
check (Pair v1 v2) = check v1 && check v2
check (Plus _ _)   = assert False
check (Var _)      = assert False
check (App _ _)    = assert False
check (Fst _)      = assert False
check (Snd _)      = assert False

---------------------------------------------------------------------
-------------------------- Wrapped Evaluator ------------------------
---------------------------------------------------------------------

--leval sto e = (s, v)
--  where (s, v) = eval sto e 
--  let _        = check_value v in
--  (s, v)

---------------------------------------------------------------------
-------------------------- Unit Tests -------------------------------
---------------------------------------------------------------------

mytests  = 
  let e1      = Const 10
      e2      = Lam "f" (Lam "g" (Lam "x" (App (Var "f")  (App (Var "g") (Var "x")))))
      e3      = Lam "x" (Plus (Var "x") e1)
      e4      = App (App e2 e3) e3
      e5      = Pair (App e4 (Const 0)) (App e4 (Const 100))
      e6      = Fst e5
      e7      = Snd e5
      emp     = []
      (_, v1) = eval emp e1
      (_, v2) = eval emp e2
      (_, v3) = eval emp e3
      (_, v4) = eval emp e4
      (_, v5) = eval emp e5
      (_, v6) = eval emp e6
      (_, v7) = eval emp e7
  in True
