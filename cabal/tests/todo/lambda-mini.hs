module LambdaEval where

-- import Data.List        (lookup)

import LiquidPrelude        

{-# ANN module "spec   lambda-mini.hs.spec" #-}
{-# ANN module "hquals lambdaEval.hs.hquals" #-}

---------------------------------------------------------------------
----------------------- Datatype Definition -------------------------
---------------------------------------------------------------------

type Bndr 
  = Int

data Expr 
  = Lam Bndr Expr
  | Var Bndr  
  | App Expr Expr

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

evalVar :: Bndr -> [(Bndr, Expr)] -> Expr
evalVar x ((y,v):sto) 
  | x `eq` y
  = v
  | otherwise
  = evalVar x sto

evalVar x []      
  = error "unbound variable"

-- A "value" is simply: {v: Expr | (? (isValue v)) } *)

eval sto (Var x)  
  = (sto, evalVar x sto)

eval sto (App e1 e2)
  = let (_,    v2 ) = eval sto e2 
        (sto1, e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval ((x, v2): sto1) e
         _         -> error "non-function application"

eval sto (Lam x e) 
  = (sto, Lam x e)

-----------------------------------------------------------------------
---------------------------- Value Checker ----------------------------
-----------------------------------------------------------------------
--
check (Lam _ _)    = True
check (Var _)      = assert False
check (App _ _)    = assert False
--
-----------------------------------------------------------------------
---------------------------- Wrapped Evaluator ------------------------
-----------------------------------------------------------------------
--
----leval sto e = (s, v)
----  where (s, v) = eval sto e 
----  let _        = check_value v in
----  (s, v)
--
-----------------------------------------------------------------------
---------------------------- Unit Tests -------------------------------
-----------------------------------------------------------------------

tests =
  let (f,g,x) = (0,1,2) 
      e1      = Lam x (Var x)
      e2      = App e1 e1 
      e3      = Lam f (Lam g (Lam x (App (Var f)  (App (Var g) (Var x)))))
      vs      = map (snd . eval []) [e1, e2, e3]
  in map check vs
