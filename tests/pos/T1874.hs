module T1874 where

{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--reflection"      @-}
{-@ LIQUID "--ple"             @-}

import Language.Haskell.Liquid.ProofCombinators

data Ty = TInt | TFun Ty Ty

{-@
type FunTy = { t : Ty | isFunTy t }
data Ty = TInt | TFun Ty Ty
@-}

{-@ measure isFunTy @-}
isFunTy :: Ty -> Bool
isFunTy (TFun _ _) = True
isFunTy _ = False

{- reflect funResTy @-}
{-@ measure funResTy @-}
{-@ funResTy :: FunTy -> Ty @-}
funResTy :: Ty -> Ty
funResTy (TFun _ b) = b

{-@ measure funArgTy @-}
{-@ funArgTy :: FunTy -> Ty @-}
funArgTy :: Ty -> Ty
funArgTy (TFun a _) = a

{-@
type FunExp = { e : Exp | isFunTy (exprType e) }
type ExpT T = { e : Exp | T = exprType e }
data Exp
  = Var Ty Int
  | Lam Ty Exp
  | App (e1 :: FunExp) (ExpT (funArgTy (exprType e1)))
@-}

data Exp
  = Var Ty Int
  | Lam Ty Exp
  | App Exp Exp

{-@ measure exprType @-}
exprType :: Exp -> Ty
exprType (Var ty _) = ty
exprType (Lam ty e) = TFun ty (exprType e)
exprType (App e1 _) = funResTy (exprType e1)


{-@ typeAppLam_prop :: ty:Ty -> e0:Exp -> e1:Exp -> { exprType (App (Lam ty e0) e1) = exprType e0 } @-}
typeAppLam_prop :: Ty -> Exp -> Exp -> Proof
typeAppLam_prop _ _ _ = trivial *** QED

{-@ step :: e:Exp -> Maybe (ExpT (exprType e)) @-}
step :: Exp -> Maybe Exp
step e0 = case e0 of
    Var{} -> Nothing
    Lam{} -> Nothing
    App e1 e2 -> case step e1 of
      Just e1' -> Just (App e1' e2)
      Nothing -> case step e2 of
        Just e2' -> Just (App e1 e2')
        Nothing -> case e1 of
          Lam ty e11 ->
              Just e11 -- ? typeAppLam_prop ty e11 e2
          _ -> Nothing
