{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Eval (eval) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Prelude hiding (lookup)
import Data.Set (Set (..))


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
eval :: Env Expr -> Expr -> Expr
-------------------------------------------------------------------
eval env i@(Const _)     = i
eval env (Var x)         = lookup x env 
eval env (Plus e1 e2)    = plus (eval env e1) (eval env e2) 
eval env (Let x e1 e2)   = eval env' e2 
  where 
    env'                 = (x, eval env e1) : env

-------------------------------------------------------------------
plus :: Expr -> Expr -> Expr
-------------------------------------------------------------------
plus (Const i) (Const j) = Const (i+j)
plus _         _         = die "Bad call to plus"


-------------------------------------------------------------------
lookup :: Bndr -> Env Expr -> Expr 
-------------------------------------------------------------------
lookup x ((y,v):env)   
  | x == y             = v
  | otherwise          = lookup x env
lookup x []            = die "Unbound Variable"




-------------------------------------------------------------------
-- | Values
-------------------------------------------------------------------

-- Lets define `Value` as a refinement of `Expr`...



-------------------------------------------------------------------
-- | Closed Expressions
-------------------------------------------------------------------

-- Lets define `ClosedExpr` as a refinement of `Expr` ...



-------------------------------------------------------------------
-- | BOILERPLATE 
-------------------------------------------------------------------

{-@ die :: {v:_ | false} -> a @-}
die x   = error x





-------------------------------------------------------------------
-- | CHEAT AREA ---------------------------------------------------
-------------------------------------------------------------------

{- lookup :: x:Bndr -> {v:Env Val | Set_mem x (vars v)} -> Val @-}

{- eval :: g:Env Val -> ClosedExpr g -> Val @-}


-- | Values

{- type Val           = {v:Expr | val v} @-}

{- measure val       :: Expr -> Prop
    val (Const i)     = true
    val (Var x)       = false
    val (Plus e1 e2)  = false
    val (Let x e1 e2) = false
  @-}

-- | Closed Expressions

{- type ClosedExpr G  = {v:Expr | Set_sub (free v) (vars G)} @-}

{- measure vars :: Env a -> (Set Bndr)
    vars ([])    = (Set_empty 0)
    vars (b:env) = (Set_cup (Set_sng (fst b)) (vars env))
  @-}

{- measure free       :: Expr -> (Set Bndr) 
    free (Const i)     = (Set_empty 0)
    free (Var x)       = (Set_sng x) 
    free (Plus e1 e2)  = (Set_cup (free e1) (free e2))
    free (Let x e1 e2) = (Set_cup (free e1) (Set_dif (free e2) (Set_sng x)))
  @-}
