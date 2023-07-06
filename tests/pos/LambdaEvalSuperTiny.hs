{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}

module LambdaEvalSuperTiny () where
import Language.Haskell.Liquid.Prelude

---------------------------------------------------------------------
----------------------- Datatype Definition -------------------------
---------------------------------------------------------------------

data Pair a b = P a b
data LL a     = Nil | Cons a (LL a)

data Bndr

data Expr
  = Lam Bndr Expr
  | Var Bndr
  | App Expr Expr

{-@
data Expr
  = Lam { eX :: Bndr, eBody :: Expr }
  | Var { eX :: Bndr                }
  | App { eF :: Expr, eArg  ::Expr  }
@-}

{-@ measure elen @-}
elen :: Expr -> Int
elen (Var x)     = 0
elen (Lam x e)   = 1 + (elen e)
elen (App e1 e2) = 1 + (elen e1) + (elen e2)

{-@ invariant {v:Expr | (elen v) >= 0} @-}

{-@  measure isValue @-}
isValue :: Expr -> Bool
isValue (Lam x e)    = True
isValue (Var x)      = False
isValue (App e1 e2)  = False

{-@ type Value = {v: Expr | (isValue v) } @-}
{-@ type Store = LL (Pair Bndr Value)       @-}

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

{-@ evalVar :: Bndr -> Store -> Value @-}
evalVar :: Bndr -> LL (Pair Bndr Expr) -> Expr
evalVar = unsafeError "HIDEME"

{-@ eval :: Store -> e:Expr -> (Pair Store Value) @-}
eval sto (Var x)
  = P sto (evalVar x sto)

eval sto (App e1 e2)
  = let (P _    v2 ) = eval sto e2
        (P sto1 e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval (Cons (P x v2) sto1) e
         _         -> unsafeError "non-function application"

eval sto (Lam x e)
  = P sto (Lam x e)
