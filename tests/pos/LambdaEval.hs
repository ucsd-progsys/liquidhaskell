{-@ LIQUID "--no-termination" @-}

module LambdaEval where

import Data.List        (lookup)

import Language.Haskell.Liquid.Prelude   

---------------------------------------------------------------------
----------------------- Datatype Definition -------------------------
---------------------------------------------------------------------

type Bndr 
  = Int

data Expr 
  = Lam Bndr Expr
  | Var Bndr  
  | App Expr Expr
  | Const Int
  | Plus Expr Expr
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr

{-@ 
data Expr [elen]
  = Lam (x::Bndr) (e::Expr)
  | Var (x::Bndr)  
  | App (e1::Expr) (e2::Expr)
  | Const (i::Int)
  | Plus (e1::Expr) (e2::Expr)
  | Pair (e1::Expr) (e2::Expr)
  | Fst (e::Expr)
  | Snd (e::Expr)
@-}

{-@ measure elen :: (Expr) -> Int
    elen(Lam x e)    = 1 + (elen e)
    elen(Var x)      = 0
    elen(App e1 e2)  = 1 + (elen e1) + (elen e2)
    elen(Const i)    = 1
    elen(Plus e1 e2) = 1 + (elen e1) + (elen e2)
    elen(Pair e1 e2) = 1 + (elen e1) + (elen e2)
    elen(Fst e)      = 1 + (elen e)
    elen(Snd e)      = 1 + (elen e)
@-}

{-@ invariant {v:Expr | (elen v) >= 0} @-}

{-@
measure isValue      :: Expr -> Prop
isValue (Const i)    = true 
isValue (Lam x e)    = true 
isValue (Var x)      = false
isValue (App e1 e2)  = false
isValue (Plus e1 e2) = false 
isValue (Fst e)      = false
isValue (Snd e)      = false
isValue (Pair e1 e2) = ((? (isValue(e1))) && (? (isValue(e2))))
@-}

{-@ type Value = {v: Expr | (? (isValue([v]))) } @-}

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

{-@ Decrease evalVar 2 @-}
evalVar :: Bndr -> [(Bndr, Expr)] -> Expr
evalVar x ((y,v):sto) 
  | x == y
  = v
  | otherwise
  = evalVar x sto

evalVar x []      
  = error "unbound variable"


{-@ Decrease eval 2 @-}
{-@ eval :: [(Bndr, Value)] -> Expr -> ([(Bndr, Value)], Value) @-}
eval sto (Const i) 
  = (sto, Const i)

eval sto (Var x)  
  = (sto, evalVar x sto) 

eval sto (Plus e1 e2)
  = let (_, e1') = eval sto e1
        (_, e2') = eval sto e2
    in case (e1, e2) of
         (Const i1, Const i2) -> (sto, Const (i1 + i2))
         _                    -> error "non-integer addition"

eval sto (App e1 e2)
  = let (_,    v2 ) = eval sto e2 
        (sto1, e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval ((x, v2): sto1) e
         _         -> error "non-function application"

eval sto (Lam x e) 
  = (sto, Lam x e)

eval sto (Pair e1 e2)
  = (sto, Pair v1 v2)
  where (_, v1) = eval sto e1
        (_, v2) = eval sto e2

eval sto (Fst e)
  = let (sto', e') = eval sto e in
    case e' of
      Pair v _ -> (sto', v)
      _        -> error "non-tuple fst"

eval sto (Snd e)
  = let (sto', e') = eval sto e in
    case e' of
      Pair _ v -> (sto', v)
      _        -> error "non-tuple snd"

---------------------------------------------------------------------
-------------------------- Value Checker ----------------------------
---------------------------------------------------------------------

{-@ assert check :: {v: Expr | (? (isValue([v]))) } -> Bool @-}
check (Const _)    = True
check (Lam _ _)    = True
check (Var _)      = liquidAssertB False
check (App _ _)    = liquidAssertB False
check (Pair v1 v2) = check v1 && check v2
check (Fst _)      = liquidAssertB False
check (Snd _)      = liquidAssertB False
check (Plus _ _)   = liquidAssertB False

---------------------------------------------------------------------
-------------------------- Unit Tests -------------------------------
---------------------------------------------------------------------

tests =
  let (f,g,x) = (0,1,2) 
      e1      = Lam x (Var x)
      e2      = App e1 e1 
      e3      = Lam f (Lam g (Lam x (App (Var f)  (App (Var g) (Var x)))))
      e4      = Const 10
      e5      = App e1 e4
      e6      = Lam x (Plus (Var x) e4)
      e7      = App (App e3 e6) e6
      e8      = Pair (App e7 (Const 0)) (App e7 (Const 100))
      e9      = Fst e8
      e10     = Snd e9
      vs      = map (snd . eval []) [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  in map check vs
