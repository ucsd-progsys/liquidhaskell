module Eval (eval) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Prelude hiding (lookup)
import Data.Set (Set (..))

data Val  = I Int
          | C Env Bndr Expr  

type Bndr = String 

data Expr = Const Int
          | Var   Bndr
          | Plus  Expr Expr
          | Let   Bndr Expr Expr
          | Lam   Bndr Expr
          | App   Expr Expr
 
type Env  = [(Bndr, Val)]

------------------------------------------------------------------
{-@ lookup :: g:Env -> (InEnv g) -> Val @-}
lookup :: Env -> Bndr -> Val
---------------------  -------------------------------------------
lookup ((y,v):env) x 
  | x == y             = v
  | otherwise          = lookup env x
lookup [] _            = liquidError "Unbound Variable"

------------------------------------------------------------------
{-@ Lazy eval @-}
{-@ eval :: env:Env -> (ClosedExpr env) -> Val @-}
------------------------------------------------------------------

eval env (Const i)     
  = I i

eval env (Var x)       
  = lookup env x 

eval env (Plus e1 e2)  
  = case (eval env e1, eval env e2) of 
      (I n1, I n2) -> I (n1 + n2) 
      _            -> error "Type Error: non-int addition"

eval env (Let x e1 e2) 
  = eval ((x, eval env e1) : env) e2 

eval env (Lam x e)
  = C env x e

eval env (App e1 e2)   
  = case eval env e1 of 
      C env1 x e1' -> eval ((x, eval env e2) : env1) e1'
      _            -> error "Type Error: non-function application"


{-@ type InEnv G      = {v:Bndr | (Set_mem v (vars G))}                              @-}
{-@ type ClosedExpr G = {v:Expr | (Set_sub (free v) (vars G))}                       @-}
{-@ type Closure G X  = {v:Expr | (Set_sub (free v) (Set_cup (vars G) (Set_sng X)))} @-}


{-@ invariant {v:Expr | (esize v) > 0} @-}

{-@ data Val  = I (i::Int)
              | C (g::Env) (x::Bndr) (e::(Closure g x))  
  @-}

{-@ data Expr [esize]
      = Const (i::Int)
      | Var   (x::Bndr)
      | Plus  (s::Expr)  (t::Expr)
      | Let   (x::Bndr)  (s::Expr) (t::Expr)
      | Lam   (x::Bndr)  (t::Expr)
      | App   (s::Expr)  (t::Expr)
  @-}

------------------------------------------------------------------
-- The set of binders in an environment --------------------------
------------------------------------------------------------------

{-@ measure vars :: Env -> (Set Bndr)
    vars ([])    = {v | (Set_emp v) }
    vars (b:env) = {v | v = (Set_cup (Set_sng (fst b)) (vars env))}
  @-}

------------------------------------------------------------------
-- The set of free-vars in an expression -------------------------
------------------------------------------------------------------

{-@ measure free       :: Expr -> (Set Bndr) 
    free (Const i)     = {v | (Set_emp v)}
    free (Var x)       = {v | v = (Set_sng x)} 
    free (Plus e1 e2)  = {v | v = (Set_cup (free e1) (free e2))}
    free (Let x e1 e2) = {v | v = (Set_cup (free e1) (Set_dif (free e2) (Set_sng x)))}
    free (App e1 e2)   = {v | v = (Set_cup (free e1) (free e2))}
    free (Lam x e)     = {v | v = (Set_dif (free e) (Set_sng x))}
  @-}

------------------------------------------------------------------
-- A Size Metric on Expressions ----------------------------------
------------------------------------------------------------------

{-@ measure esize       :: Expr -> Int 
    esize (Var x)       = 1
    esize (Const i)     = 1
    esize (Plus e1 e2)  = (esize e1) + (esize e2)
    esize (Let x e1 e2) = (esize e1) + (esize e2)
  @-}
