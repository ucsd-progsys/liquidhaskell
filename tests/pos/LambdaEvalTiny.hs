{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}

module LambdaEvalMini () where
import Language.Haskell.Liquid.Prelude 

---------------------------------------------------------------------
----------------------- Datatype Definition -------------------------
---------------------------------------------------------------------

data Bndr

data Expr
  = Lam Bndr Expr
  | Var Bndr
  | App Expr Expr

{-@
data Expr [elen]
  = Lam { eX :: Bndr, eBody :: Expr }
  | Var { eX :: Bndr                }
  | App { eF :: Expr, eArg  ::Expr  }
@-}

{-@ measure elen :: Expr -> Int
    elen (Var x)     = 0
    elen (Lam x e)   = 1 + (elen e)
    elen (App e1 e2) = 1 + (elen e1) + (elen e2)
  @-}

{-@ invariant {v:Expr | (elen v) >= 0} @-}

{-@  measure isValue :: Expr -> Bool
     isValue (Lam x e)    = true
     isValue (Var x)      = false
     isValue (App e1 e2)  = false
  @-}

{-@ type Value = {v: Expr | isValue v } @-}
{-@ type Store = [(Bndr, Value)]            @-}

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

{-@ evalVar :: Bndr -> Store -> Value @-}
evalVar :: Bndr -> [(Bndr, Expr)] -> Expr
evalVar = unsafeError "HIDEME"

{-@ decrease eval 2 @-}

{-@ eval :: sto:Store -> e:Expr -> (Store, Value) @-}

eval sto (Var x)
  = (sto, evalVar x sto)

eval sto (App e1 e2)
  = let (_,    v2 ) = eval sto e2
        (sto1, e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval ((x, v2) : sto1) e
         _         -> unsafeError "non-function application"

eval sto (Lam x e)
  = (sto, Lam x e)
