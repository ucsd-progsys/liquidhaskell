module T1396_1 where

data AExp
  = N Int
  | V String
  | Plus AExp AExp

subst :: String -> AExp -> AExp -> AExp
subst x e (Plus  a1 a2)  = Plus  (subst x e a1) (subst x e a2)
subst x e (V y) | x == y = e
subst _ _ a              = a
