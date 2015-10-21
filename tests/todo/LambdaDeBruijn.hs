module LambdaDeBruijn where

{-@ LIQUID "--native" @-}
type Var = Int
data Typ
data Expr = EVar Var
          | ELam Typ Expr
          | EUnit
          | EApp Expr Expr

{-@ autosize Expr @-}

{-@measure isVar @-}
isVar :: Expr -> Bool
isVar (EVar _) = True
isVar _        = False
