module LambdaEval where

data Expr = Lam Int Expr | App

eval e = e1
  where Lam x e1 = eval e 


