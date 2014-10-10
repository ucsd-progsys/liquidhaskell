{-@ LIQUID "--no-termination" @-}

module Eval (eval) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Prelude hiding (lookup)
import Data.Set (Set (..))

{-@ embed Set as Set_Set @-}

type Val  = Int

type Bndr = String 

data Expr = Const Int
          | Var   Bndr
          | Plus  Expr Expr
          | Let   Bndr Expr Expr

type Env  = [(Bndr, Val)]

------------------------------------------------------------------
{-@ lookup :: x:Bndr -> {v:Env | Set_mem x (vars v)} -> Val @-}
lookup :: Bndr -> Env -> Val
---------------------  -------------------------------------------
lookup x ((y,v):env)   
  | x == y             = v
  | otherwise          = lookup x env
lookup x []            = liquidError "Unbound Variable"

------------------------------------------------------------------
{-@ eval :: g:Env -> CExpr g -> Val @-}
------------------------------------------------------------------
eval env (Const i)     = i
eval env (Var x)       = lookup x env 
eval env (Plus e1 e2)  = eval env e1 + eval env e2 
eval env (Let x e1 e2) = eval env' e2 
  where 
    env'               = (x, eval env e1) : env

{-@ type CExpr G = {v:Expr | Set_sub (free v) (vars G)} @-}

{-@ measure vars :: Env -> (Set Bndr)
    vars ([])    = {v | Set_emp v }
    vars (b:env) = {v | v = Set_cup (Set_sng (fst b)) (vars env)}
  @-}

{-@ measure free       :: Expr -> (Set Bndr) 
    free (Const i)     = {v | Set_emp v}
    free (Var x)       = {v | v = Set_sng x} 
    free (Plus e1 e2)  = {v | v = Set_cup (free e1) (free e2)}
    free (Let x e1 e2) = {v | v = Set_cup (free e1) (Set_dif (free e2) (Set_sng x))}
  @-}
