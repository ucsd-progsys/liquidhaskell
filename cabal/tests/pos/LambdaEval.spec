module spec LambdaEval where

measure isValue      :: Expr -> Bool
isValue (Const i)    = true 
isValue (Lam x e)    = true 
isValue (Var x)      = false
isValue (App e1 e2)  = false
isValue (Plus e1 e2) = false 
isValue (Fst e)      = false
isValue (Snd e)      = false
isValue (Pair e1 e2) = ((? (isValue(e1))) && (? (isValue(e2))))
