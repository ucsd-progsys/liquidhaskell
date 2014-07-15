{-@ LIQUID "--no-termination" @-}

module LambdaEvalMini () where

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
{-@
data Expr [elen] 
  = Lam (x::Bndr) (e::Expr)
  | Var (x::Bndr)  
  | App (e1::Expr) (e2::Expr)
@-}

{-@ measure elen :: Expr -> Int
    elen(Var x)     = 0
    elen(Lam x e)   = 1 + (elen e) 
    elen(App e1 e2) = 1 + (elen e1) + (elen e2) 
  @-}

{-@ invariant {v:Expr | (elen v) >= 0} @-}

{-@  measure isValue :: Expr -> Prop
     isValue (Lam x e)    = true 
     isValue (Var x)      = false
     isValue (App e1 e2)  = false
  @-}

{-@ type Value = {v: Expr | isValue v } @-}

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

evalVar x ((y, v):sto) 
  | x == y
  = v
  | otherwise
  = evalVar x sto

evalVar x []      
  = error "unbound variable"

-- A "value" is simply: {v: Expr | isValue v } *)

{-@ Decrease eval 2 @-}
{-@ eval :: [(Bndr, Value)] -> Expr -> ([(Bndr, Value)], Value) @-}

eval sto (Var x)  
  = (sto, evalVar x sto)

eval sto (App e1 e2)
  = let (_,    v2 ) = eval sto e2 
        (sto1XXX, e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval ((x, v2): sto1XXX) e
         _         -> error "non-function application"

eval sto (Lam x e) 
  = (sto, Lam x e)

-----------------------------------------------------------------------
---------------------------- Value Checker ----------------------------
-----------------------------------------------------------------------

check (Lam _ _)    = True
check (Var _)      = liquidAssertB False
check (App _ _)    = liquidAssertB False

-----------------------------------------------------------------------
---------------------------- Unit Tests -------------------------------
-----------------------------------------------------------------------
mysnd (x, y) = y
tests =
  let (f,g,x) = (0,1,2) 
      e1      = Lam x (Var x)
      e2      = App e1 e1 
      e3      = Lam f (Lam g (Lam x (App (Var f)  (App (Var g) (Var x)))))
      vs      = map (mysnd . eval []) [e1, e2, e3]
  in map check vs
