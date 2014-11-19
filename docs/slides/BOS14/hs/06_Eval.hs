{-@ LIQUID "--no-termination" @-}

module Eval (eval) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Prelude hiding (lookup)
import Data.Set (Set (..))

lookup :: Bndr -> Env Expr -> Expr 

-------------------------------------------------------------------
-- | Binders, Expressions, Environments
-------------------------------------------------------------------

type Bndr = String 

data Expr = Const Int
          | Var   Bndr
          | Plus  Expr Expr
          | Let   Bndr Expr Expr

type Env a = [(Bndr, a)]

-------------------------------------------------------------------
-- | Values
-------------------------------------------------------------------

{-@ type Val = {v:Expr | val v} @-}

{-@ measure val       :: Expr -> Prop
    val (Const i)     = true
    val (Var x)       = false
    val (Plus e1 e2)  = false
    val (Let x e1 e2) = false
  @-}

-------------------------------------------------------------------
{-@ lookup :: x:Bndr -> {v:Env Val | Set_mem x (vars v)} -> Val @-}
-------------------------------------------------------------------
lookup x ((y,v):env)   
  | x == y             = v
  | otherwise          = lookup x env
lookup x []            = liquidError "Unbound Variable"

-------------------------------------------------------------------
{-@ eval :: g:Env Val -> ClosedExpr g -> Val @-}
-------------------------------------------------------------------
eval env i@(Const _)   = i
eval env (Var x)       = lookup x env 
eval env (Plus e1 e2)  = plus (eval env e1) (eval env e2) 
eval env (Let x e1 e2) = eval env' e2 
  where 
    env'               = (x, eval env e1) : env

plus (Const i) (Const j) = Const (i+j)
plus _         _         = liquidError "Bad call to plus"


{-@ type ClosedExpr G  = {v:Expr | Set_sub (free v) (vars G)} @-}

{-@ measure vars :: Env a -> (Set Bndr)
    vars ([])    = (Set_empty 0)
    vars (b:env) = (Set_cup (Set_sng (fst b)) (vars env))
  @-}

{-@ measure free       :: Expr -> (Set Bndr) 
    free (Const i)     = (Set_empty 0)
    free (Var x)       = (Set_sng x) 
    free (Plus e1 e2)  = (Set_cup (free e1) (free e2))
    free (Let x e1 e2) = (Set_cup (free e1) (Set_dif (free e2) (Set_sng x)))
  @-}
