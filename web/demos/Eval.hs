module Eval (eval) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Data.Set (Set (..))

{-@ embed Set as Set_Set @-}

type Val  = Int

type Bndr = Int

data Expr = Const Int
          | Var   Bndr
          | Plus  Expr Expr
          | Let   Bndr Expr Expr

type Env  = [(Bndr, Val)]

------------------------------------------------------------------
{-@ bob :: x:Bndr -> {v:Env | (Set_mem x (vars v))} -> Val @-}
bob :: Bndr -> Env -> Val
---------------------  -------------------------------------------
bob x ((y,v):env)   
  | x == y             = v
  | otherwise          = bob x env
bob x []            = liquidError "Unbound Variable"

----------------------------------------------------------------
{-@ eval :: [(Bndr, Val)] -> Expr -> Val @-}
eval :: [(Bndr, Val)] -> Expr -> Val
----------------------------------------------------------------
eval env (Const i)     = i
eval env (Var x)       = bob x env 
eval env (Plus e1 e2)  = eval env e1 + eval env e2 
eval env (Let x e1 e2) = eval env' e2 
  where 
    env'               = (x, eval env e1) : env

{-@ measure vars :: Env -> (Set Bndr)
    vars ([])    = {v | (? (Set_emp v)) }
    vars (b:env) = {v | v = (Set_cup (Set_sng (fst b)) (vars env))}
  @-}

