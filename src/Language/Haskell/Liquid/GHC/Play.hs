{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.

module Language.Haskell.Liquid.GHC.Play where

import Prelude hiding (error)

import           Control.Arrow       ((***))
import qualified Data.HashMap.Strict as M
import qualified Data.List           as L
import qualified Data.Maybe          as Mb 

import Language.Haskell.Liquid.GHC.API as Ghc hiding (substTysWith, panic,showPpr)
import Language.Haskell.Liquid.GHC.Misc ()
import Language.Haskell.Liquid.Types.Errors


-------------------------------------------------------------------------------
-- | Positivity Checker -------------------------------------------------------
-------------------------------------------------------------------------------

getNonPositivesTyCon :: [TyCon] -> [(TyCon, [DataCon])]
getNonPositivesTyCon tcs = Mb.catMaybes $ map go (M.toList $ makeAppearences tcs)
  where 
    go (tc,dcocs) = case filter (\(_,occ) -> elem tc (negA occ)) dcocs of  
                      [] -> Nothing
                      xs -> Just (tc, fst <$> xs) 

data TyConAppearance = TyConA {posA :: [TyCon], negA :: [TyCon] }
  deriving Eq

instance Monoid TyConAppearance where 
  mempty = TyConA mempty mempty 
instance Semigroup TyConAppearance where 
  TyConA p1 n1 <> TyConA p2 n2 = TyConA (L.nub (p1 <> p2)) (L.nub (n1 <> n2))
instance Outputable TyConAppearance where
  ppr (TyConA pos neg) = text "pos" <+> ppr pos <+>  text "neg" <+> ppr neg


-- Keep track of appearances of each DataCon for a better error message
type ApprearanceMap = M.HashMap TyCon [(DataCon, TyConAppearance)] 

instance Outputable ApprearanceMap where
  ppr m = ppr (M.toList m)


makeAppearences :: [TyCon] -> ApprearanceMap 
makeAppearences tycons 
  = let m0 = M.fromList [(tc, map (\dc -> (dc, makeAppearence (dctypes dc))) (tyConDataCons tc)) 
                        | tc <- tycons']
    -- fixpoint to find appearanced of mutually recursive data definitons
    in fix (\m -> foldl merge m tycons') m0 
  where 
    fix f x = let x' = f x in if x == x' then x else fix f x' 
    merge m tc = M.update (mergeList m) tc m 
    mergeList m xs = Just [(dc, mergeApp m am) | (dc,am) <- xs]
    mergeApp m (TyConA pos neg) = 
        let TyConA pospos posneg = mconcat (findAppearence m <$> pos)
            TyConA negpos negneg = mconcat (findAppearence m <$> neg) 
        -- Keep positive, flip negative 
        in TyConA (L.nub (pos <> pospos <> negneg)) (L.nub (neg <> negpos <> posneg))


    tycontypes tc = concatMap dctypes $ tyConDataCons tc
    dctypes    dc = irrelevantMult <$> dataConOrigArgTys dc

    -- Construct the map for all TyCons that appear in the definitions 
    tycons' = L.nub ((concatMap tcs (concat (tycontypes <$> tycons))) ++ tycons) 

    tcs (TyConApp tc' ts) = tc':(concatMap tcs ts)
    tcs (AppTy t1 t2)     = tcs t1 ++ tcs t2 
    tcs (ForAllTy _ t)    = tcs t 
    tcs (FunTy _ _ t1 t2) = tcs t1 ++ tcs t2 
    tcs (TyVarTy _ )      = [] 
    tcs (LitTy _)         = [] 
    tcs (CastTy _ _)      = [] 
    tcs (CoercionTy _)    = []  

makeAppearence :: [Type] -> TyConAppearance 
makeAppearence ts = foldl (go 1) mempty ts 
  where 
    go :: Int -> TyConAppearance -> Type -> TyConAppearance
    go p m (TyConApp tc ts)  = addAppearence p tc $ foldl (go p) m ts 
    go _ m (TyVarTy _ )      = m 
    go _ m (AppTy t1 t2)     = go 0 (go 0 m t1) t2  
    go p m (ForAllTy _ t)    = go p m t 
    go p m (FunTy _ _ t1 t2) = go p (go (-p) m t1) t2 
    go _ m (LitTy _)         = m 
    go _ m (CastTy _ _)      = m  
    go _ m (CoercionTy _)    = m   

    addAppearence p tc (TyConA pos neg)  
      | p > 0     = TyConA (L.nub (tc:pos)) neg  
      | p < 0     = TyConA pos (L.nub (tc:neg))  
      | otherwise = TyConA (L.nub (tc:pos)) (L.nub (tc:neg))  

findAppearence :: ApprearanceMap -> TyCon -> TyConAppearance
findAppearence m tc = mconcat (snd <$> M.lookupDefault mempty tc m)




isRecursivenewTyCon :: TyCon -> Bool 
isRecursivenewTyCon c 
  | not (isNewTyCon c)
  = False 
isRecursivenewTyCon c 
  = go t 
  where 
    t = snd $ newTyConRhs c
    go (AppTy t1 t2)      = go t1 || go t2 
    go (TyConApp c' ts)   = c == c' || any go ts 
    go (ForAllTy _ t1)    = go t1 
    go (FunTy _ _ t1 t2)  = go t1 || go t2
    go (CastTy t1 _)      = go t1 
    go _                  = False   
  

isHoleVar :: Var -> Bool 
isHoleVar x = L.isPrefixOf "_" (show x)

dataConImplicitIds :: DataCon -> [Id]
dataConImplicitIds dc = [ x | AnId x <- dataConImplicitTyThings dc]

class Subable a where
  sub   :: M.HashMap CoreBndr CoreExpr -> a -> a
  subTy :: M.HashMap TyVar Type -> a -> a

instance Subable CoreExpr where
  sub s (Var v)        = M.lookupDefault (Var v) v s
  sub _ (Lit l)        = Lit l
  sub s (App e1 e2)    = App (sub s e1) (sub s e2)
  sub s (Lam b e)      = Lam b (sub s e)
  sub s (Let b e)      = Let (sub s b) (sub s e)
  sub s (Case e b t a) = Case (sub s e) (sub s b) t (map (sub s) a)
  sub s (Cast e c)     = Cast (sub s e) c
  sub s (Tick t e)     = Tick t (sub s e)
  sub _ (Type t)       = Type t
  sub _ (Coercion c)   = Coercion c

  subTy s (Var v)      = Var (subTy s v)
  subTy _ (Lit l)      = Lit l
  subTy s (App e1 e2)  = App (subTy s e1) (subTy s e2)
  subTy s (Lam b e)    | isTyVar b = Lam v' (subTy s e)
   where v' = case M.lookup b s of
               Just (TyVarTy v) -> v
               _                -> b

  subTy s (Lam b e)      = Lam (subTy s b) (subTy s e)
  subTy s (Let b e)      = Let (subTy s b) (subTy s e)
  subTy s (Case e b t a) = Case (subTy s e) (subTy s b) (subTy s t) (map (subTy s) a)
  subTy s (Cast e c)     = Cast (subTy s e) (subTy s c)
  subTy s (Tick t e)     = Tick t (subTy s e)
  subTy s (Type t)       = Type (subTy s t)
  subTy s (Coercion c)   = Coercion (subTy s c)

instance Subable Coercion where
  sub _ c                = c
  subTy _ _              = panic Nothing "subTy Coercion"

instance Subable (Alt Var) where
 sub s (a, b, e)   = (a, map (sub s) b,   sub s e)
 subTy s (a, b, e) = (a, map (subTy s) b, subTy s e)

instance Subable Var where
 sub s v   | M.member v s = subVar $ s M.! v
           | otherwise    = v
 subTy s v = setVarType v (subTy s (varType v))

subVar :: Expr t -> Id
subVar (Var x) = x
subVar  _      = panic Nothing "sub Var"

instance Subable (Bind Var) where
 sub s (NonRec x e)   = NonRec (sub s x) (sub s e)
 sub s (Rec xes)      = Rec ((sub s *** sub s) <$> xes)

 subTy s (NonRec x e) = NonRec (subTy s x) (subTy s e)
 subTy s (Rec xes)    = Rec ((subTy s  *** subTy s) <$> xes)

instance Subable Type where
 sub _ e   = e
 subTy     = substTysWith

substTysWith :: M.HashMap Var Type -> Type -> Type
substTysWith s tv@(TyVarTy v)      = M.lookupDefault tv v s
substTysWith s (FunTy aaf m t1 t2) = FunTy aaf m (substTysWith s t1) (substTysWith s t2)
substTysWith s (ForAllTy v t)      = ForAllTy v (substTysWith (M.delete (binderVar v) s) t)
substTysWith s (TyConApp c ts)     = TyConApp c (map (substTysWith s) ts)
substTysWith s (AppTy t1 t2)       = AppTy (substTysWith s t1) (substTysWith s t2)
substTysWith _ (LitTy t)           = LitTy t
substTysWith s (CastTy t c)        = CastTy (substTysWith s t) c
substTysWith _ (CoercionTy c)      = CoercionTy c 

substExpr :: M.HashMap Var Var -> CoreExpr -> CoreExpr
substExpr s = go 
  where
    subsVar v                = M.lookupDefault v v s
    go (Var v)               = Var $ subsVar v
    go (Lit l)               = Lit l 
    go (App e1 e2)           = App (go e1) (go e2) 
    go (Lam x e)             = Lam (subsVar x) (go e)
    go (Let (NonRec x ex) e) = Let (NonRec (subsVar x) (go ex)) (go e) 
    go (Let (Rec xes) e)     = Let (Rec [(subsVar x, go e) | (x,e) <- xes]) (go e)
    go (Case e b t alts)     = Case (go e) (subsVar b) t [(c, subsVar <$> xs, go e) | (c, xs, e) <- alts]
    go (Cast e c)            = Cast (go e) c 
    go (Tick t e)            = Tick t (go e)
    go (Type t)              = Type t 
    go (Coercion c)          = Coercion c 

mapType :: (Type -> Type) -> Type -> Type
mapType f = go
  where
    go t@(TyVarTy _)        = f t
    go (AppTy t1 t2)        = f $ AppTy (go t1) (go t2)
    go (TyConApp c ts)      = f $ TyConApp c (go <$> ts)
    go (FunTy aaf m t1 t2)  = f $ FunTy aaf m (go t1) (go t2)
    go (ForAllTy v t)       = f $ ForAllTy v (go t)
    go t@(LitTy _)          = f t
    go (CastTy t c)         = CastTy (go t) c
    go (CoercionTy c)       = f $ CoercionTy c 


stringClassArg :: Type -> Maybe Type
stringClassArg t | isFunTy t 
  = Nothing
stringClassArg t
  = case (tyConAppTyCon_maybe t, tyConAppArgs_maybe t) of
      (Just c, Just [t]) | isStringClassName == tyConName c
           -> Just t
      _    -> Nothing
