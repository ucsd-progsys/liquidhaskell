module spec LambdaEvalMini where

measure isValue :: Expr -> Bool
isValue (Lam x e)    = true 
isValue (Var x)      = false
isValue (App e1 e2)  = false
