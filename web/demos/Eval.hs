module Eval (eval) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Prelude hiding (lookup)

type Val  = Int

type Bndr = Int

data Expr = Const Int
          | Var   Bndr
          | Plus  Expr Expr
          | Let   Bndr Expr Expr

type Env  = [(Bndr, Val)]

----------------------------------------------------------------
lookup                 :: Bndr -> Env -> Val
---------------------  -------------------------------------------
lookup x ((y,v):env)   
  | x == y             = v
  | otherwise          = lookup x env
lookup x []            = liquidError "Unbound Variable"

----------------------------------------------------------------
eval :: Env -> Expr -> Val
----------------------------------------------------------------
eval env (Const i)     = i
eval env (Var x)       = lookup x env 
eval env (Plus e1 e2)  = eval env e1 + eval env e2 
eval env (Let x e1 e2) = eval env' e2 
  where 
    env'               = (x, eval env e1) : env

