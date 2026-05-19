{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.

module Language.Haskell.Liquid.GHC.Play where

import Prelude hiding (error)

import qualified Data.HashMap.Strict as M
import qualified Data.List           as L
import qualified Data.Maybe          as Mb

import Liquid.GHC.API as Ghc
import Language.Haskell.Liquid.GHC.Misc ()
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
