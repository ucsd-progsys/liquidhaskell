module LambdaDeBruijn where

{- Proving Termination of Parallel Substitutions,
   see  § 3.2.2 of Dependent Types and Multi Monadic Effects in F*
 -}

import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--native"   @-}
{-@ LIQUID "--totality" @-}

type Var = Int
{-@ type EVar = {v:Expr| isEVar v} @-}

type Subst = [(Var,Expr)]
{-@ type RenamingSubst = {su: [(Var,Expr)] | isRenaming su} @-}

data Typ

data Expr = EVar Var
          | ELam Typ Expr
          | EUnit
          | EApp Expr Expr
{-@ data Expr [elen] @-}

{-@ type MEVar E SU = {e:Expr | if (isEVar E && isRenaming SU) then (isEVar e) else true } @-}

{-@ sub :: su:Subst -> v:Var -> {v:Expr | if (isRenaming su) then (isEVar v) else true } @-}
sub [] v                       = EVar v
sub ((vx, x):su) v | v == vx   = x
                   | otherwise = sub su v


{-@ subst :: e:Expr -> su:Subst -> MEVar e su / [if (isEVar e) then 0 else 1, if (isRenaming su) then 0 else 1, elen e] @-}
subst EUnit        su = EUnit
subst (EVar v)     su = sub su v
subst (EApp e1 e2) su = EApp (subst e1 su) (subst e2 su)

subst (ELam t e)   su | isRenaming su =
  let su' =  toRem $ (0, EVar 0): map (\i -> (i, subst (sub su (i-1)) $ incrsubst ())) [1..]
  in ELam t $ subst e su'

subst (ELam t e)   su = -- | not $ isRenaming su
    let su' =  (0, EVar 0): map (\i -> (i, subst (sub su (i-1)) $ incrsubst ())) [1..]
    in ELam t $ subst e su'




{-@ incrsubst :: () -> RenamingSubst @-}
incrsubst :: () -> Subst
incrsubst _ = toRem $  map (\i -> (i, EVar $ i+1)) [0..]

{-@ measure isEVar @-}
isEVar :: Expr -> Bool
isEVar (EVar _) = True
isEVar _        = False



toRem :: Subst -> Subst
{-@ toRem :: [(Var, EVar)] -> RenamingSubst @-}
toRem [] = []
toRem ((x, y):sus) = (x, y):toRem sus


{-@ measure isRenaming @-}
isRenaming :: Subst -> Bool
isRenaming (vx:sus) = isEVar (mysnd vx) && isRenaming sus
isRenaming [] = True

{-@ measure mysnd @-}
mysnd (_,y) = y

{-@ invariant {v:Expr | elen v >= 0 } @-}
{-@ measure elen @-}
elen :: Expr -> Int
elen EUnit    = 0
elen (EVar v) = 0
elen (ELam _ e) = 1 + elen e
elen (EApp e1 e2) = 1 + elen e1 + elen e2
