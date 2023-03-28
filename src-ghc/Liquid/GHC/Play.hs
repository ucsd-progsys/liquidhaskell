{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.

module Liquid.GHC.Play where

import Prelude hiding (error)

import           Control.Arrow       ((***))
import qualified Data.HashMap.Strict as M
import qualified Data.List           as L
import qualified Data.Maybe          as Mb

import Liquid.GHC.API as Ghc hiding (substTysWith, panic,showPpr)
import Liquid.GHC.Misc ()
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.Variance

-------------------------------------------------------------------------------
-- | Positivity Checker -------------------------------------------------------
-------------------------------------------------------------------------------

-- If the type constructor T is in the input list and its data constructors Di, Dj
-- use T in non strictly positive positions, 
-- then (T,(Di, Dj)) will appear in the result list.  

getNonPositivesTyCon :: [TyCon] -> [(TyCon, [DataCon])]
getNonPositivesTyCon tcs = Mb.mapMaybe go (M.toList $ makeOccurrences tcs)
  where
    go (tc,dcocs) = case filter (\(_,occ) -> elem tc (negOcc occ)) dcocs of
                      [] -> Nothing
                      xs -> Just (tc, fst <$> xs)


-- OccurrenceMap maps type constructors to their TyConOccurrence. 
-- for each of their data constructor. For example, for the below data definition
-- data T a = P (T a) | N (T a -> Int) | Both (T a -> T a) | None 
-- the entry below should get generated
--  OccurrenceMap 
-- = T |-> [(P, [
--          (P,    TyConOcc [T] [])
--          (N,    TyConOcc [Int] [T])
--          (Both, TyConOcc [T] [T])
--          (None, TyConOcc [] [])
--         ])] 
-- For positivity check, ultimately we only care about self occurences, 
-- but we keep track of all the TyCons for the mutually inductive data types. 
-- We separate the occurences per data constructor only to provide better error messages. 
type OccurrenceMap = M.HashMap TyCon [(DataCon, TyConOccurrence)]

data TyConOccurrence
    = TyConOcc { posOcc :: [TyCon] -- TyCons that occur in positive positions
               , negOcc :: [TyCon] -- TyCons that occur in negative positions
               }
  deriving Eq

instance Monoid TyConOccurrence where
  mempty = TyConOcc mempty mempty
instance Semigroup TyConOccurrence where
  TyConOcc p1 n1 <> TyConOcc p2 n2 = TyConOcc (L.nub (p1 <> p2)) (L.nub (n1 <> n2))
instance Outputable TyConOccurrence where
  ppr (TyConOcc pos neg) = text "pos" <+> ppr pos <+>  text "neg" <+> ppr neg


instance Outputable OccurrenceMap where
  ppr m = ppr (M.toList m)


makeOccurrences :: [TyCon] -> OccurrenceMap
makeOccurrences tycons
  = let m0 = M.fromList [(tc, map (\dc -> (dc, makeOccurrence tcInfo (dctypes dc))) (tyConDataCons tc))
                        | tc <- tycons']
    -- fixpoint to find occurrences of mutually recursive data definitons
    in fix (\m -> foldl merge m tycons') m0
  where
    fix f x = let x' = f x in if x == x' then x else fix f x'
    tcInfo = M.fromList $ zip tycons' (makeTyConVariance <$> tycons')
    merge m tc = M.update (mergeList m) tc m
    mergeList m xs = Just [(dc, mergeApp m am) | (dc,am) <- xs]
    mergeApp m (TyConOcc pos neg) =
        let TyConOcc pospos posneg = mconcat (findOccurrence m <$> pos)
            TyConOcc negpos negneg = mconcat (findOccurrence m <$> neg)
        -- Keep positive, flip negative 
        in TyConOcc (L.nub (pos <> pospos <> negneg)) (L.nub (neg <> negpos <> posneg))


    tycontypes tc = concatMap dctypes $ tyConDataCons tc
    dctypes    dc = irrelevantMult <$> dataConOrigArgTys dc

    -- Construct the map for all TyCons that appear in the definitions 
    tycons' = L.nub (concatMap tcs (concatMap tycontypes tycons) ++ tycons)

    tcs (TyConApp tc' ts) = tc': concatMap tcs ts
    tcs (AppTy t1 t2)     = tcs t1 ++ tcs t2
    tcs (ForAllTy _ t)    = tcs t
    tcs (FunTy _ _ t1 t2) = tcs t1 ++ tcs t2
    tcs (TyVarTy _ )      = []
    tcs (LitTy _)         = []
    tcs (CastTy _ _)      = []
    tcs (CoercionTy _)    = []

makeOccurrence :: M.HashMap TyCon VarianceInfo -> [Type] -> TyConOccurrence
makeOccurrence tcInfo = foldl (go Covariant) mempty
  where
    go :: Variance -> TyConOccurrence -> Type -> TyConOccurrence
    go p m (TyConApp tc ts)  = addOccurrence p tc
                             $ foldl (\m' (t, v) -> go (v <> p) m' t) m
                                (zip ts (M.lookupDefault (repeat Bivariant) tc tcInfo))
    go _ m (TyVarTy _ )      = m
    go _ m (AppTy t1 t2)     = go Bivariant (go Bivariant m t1) t2
    go p m (ForAllTy _ t)    = go p m t
    go p m (FunTy _ _ t1 t2) = go p (go (flipVariance p) m t1) t2
    go _ m (LitTy _)         = m
    go _ m (CastTy _ _)      = m
    go _ m (CoercionTy _)    = m

    addOccurrence p tc (TyConOcc pos neg)
      = case p of
         Covariant     -> TyConOcc (L.nub (tc:pos)) neg
         Contravariant -> TyConOcc pos (L.nub (tc:neg))
         Bivariant     -> TyConOcc (L.nub (tc:pos)) (L.nub (tc:neg))
         Invariant     -> TyConOcc pos neg

findOccurrence :: OccurrenceMap -> TyCon -> TyConOccurrence
findOccurrence m tc = mconcat (snd <$> M.lookupDefault mempty tc m)




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
 sub s (Alt a b e)   = Alt a (map (sub s) b)   (sub s e)
 subTy s (Alt a b e) = Alt a (map (subTy s) b) (subTy s e)

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
    go (Let (Rec xes) e)     = Let (Rec [(subsVar x', go e') | (x',e') <- xes]) (go e)
    go (Case e b t alts)     = Case (go e) (subsVar b) t [Alt c (subsVar <$> xs) (go e') | Alt c xs e' <- alts]
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
      (Just c, Just [t']) | isStringClassName == tyConName c
           -> Just t'
      _    -> Nothing
