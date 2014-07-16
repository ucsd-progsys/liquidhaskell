{-@ LIQUID "--no-termination" @-}

module LambdaEvalMini () where

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
{-@ type Store = [(Bndr, Value)]            @-}

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

{-@ evalVar :: Bndr -> Store -> Value @-}
evalVar :: Bndr -> [(Bndr, Expr)] -> Expr 
evalVar = error "HIDEME"

{-@ Decrease eval 2 @-}

{-@ eval :: sto:Store -> e:Expr -> (Store, Value) @-}

eval sto (Var x)  
  = (sto, evalVar x sto)

eval sto (App e1 e2)
  = let (_,    v2 ) = eval sto e2 
        (sto1, e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval ((x, v2) : sto1) e
         _         -> error "non-function application"

eval sto (Lam x e) 
  = (sto, Lam x e)

