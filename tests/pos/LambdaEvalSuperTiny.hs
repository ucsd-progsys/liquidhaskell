module LambdaEvalMini where

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

{-@  measure isValue :: Expr -> Prop
     isValue (Lam x e)    = true 
     isValue (Var x)      = false
     isValue (App e1 e2)  = false
  @-}

{-@ type Value = {v: Expr | ? (isValue v) } @-}
{-@ type Store = LL (Pair Bndr Value)       @-}

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

{-@ evalVar :: Bndr -> Store -> Value @-}
evalVar :: Bndr -> LL (Pair Bndr Expr) -> Expr 
evalVar = error "HIDEME"

{-@ eval :: sto:Store -> e:Expr -> (Pair Store Value) @-}

eval sto (Var x)  
  = P sto (evalVar x sto)

eval sto (App e1 e2)
  = let (P _    v2 ) = eval sto e2 
        (P sto1 e1') = eval sto e1
    in case e1' of
         (Lam x e) -> eval (Cons (P x v2) sto1) e
         _         -> error "non-function application"

eval sto (Lam x e) 
  = P sto (Lam x e)

