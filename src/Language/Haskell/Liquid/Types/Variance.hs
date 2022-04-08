{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingVia        #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}


module Language.Haskell.Liquid.Types.Variance ( 
  Variance(..), VarianceInfo, makeTyConVariance, flipVariance 
  ) where

import Prelude hiding (error)
import Control.DeepSeq
import Data.Typeable hiding (TyCon)
import Data.Data     hiding (TyCon)
import GHC.Generics
import Data.Binary
import Data.Hashable
import Text.PrettyPrint.HughesPJ

import           Data.Maybe                (fromJust)
import qualified Data.List               as L
import qualified Data.HashSet            as S

import qualified Language.Fixpoint.Types as F

import           Language.Haskell.Liquid.Types.Generics
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import           Language.Haskell.Liquid.GHC.API        as Ghc hiding (text)

type VarianceInfo = [Variance]

data Variance = Invariant | Bivariant | Contravariant | Covariant
              deriving (Eq, Data, Typeable, Show, Generic)
              deriving Hashable via Generically Variance

flipVariance :: Variance -> Variance
flipVariance Invariant     = Invariant
flipVariance Bivariant     = Bivariant
flipVariance Contravariant = Covariant
flipVariance Covariant     = Contravariant

instance Semigroup Variance where 
  Bivariant     <> _         = Bivariant
  _             <> Bivariant = Bivariant
  Invariant     <> v         = v
  v             <> Invariant = v
  Covariant     <> v         = v
  Contravariant <> v         = flipVariance v

instance Monoid Variance where 
  mempty = Bivariant

instance Binary Variance
instance NFData Variance
instance F.PPrint Variance where
  pprintTidy _ = text . show



makeTyConVariance :: TyCon -> VarianceInfo
makeTyConVariance c = varSignToVariance <$> tvs
  where
    tvs = GM.tyConTyVarsDef c

    varsigns = if Ghc.isTypeSynonymTyCon c
                  then go True (fromJust $ Ghc.synTyConRhs_maybe c)
                  else L.nub $ concatMap goDCon $ Ghc.tyConDataCons c

    varSignToVariance v = case filter (\p -> GM.showPpr (fst p) == GM.showPpr v) varsigns of
                            []       -> Invariant
                            [(_, b)] -> if b then Covariant else Contravariant
                            _        -> Bivariant


    goDCon dc = concatMap (go True) (map irrelevantMult $ Ghc.dataConOrigArgTys dc)

    go pos (FunTy _ _ t1 t2) = go (not pos) t1 ++ go pos t2
    go pos (ForAllTy _ t)    = go pos t
    go pos (TyVarTy v)       = [(v, pos)]
    go pos (AppTy t1 t2)     = go pos t1 ++ go pos t2
    go pos (TyConApp c' ts)
       | c == c'
       = []

-- NV fix that: what happens if we have mutually recursive data types?
-- now just provide "default" Bivariant for mutually rec types.
-- but there should be a finer solution
       | mutuallyRecursive c c'
       = concatMap (goTyConApp pos Bivariant) ts
       | otherwise
       = concat $ zipWith (goTyConApp pos) (makeTyConVariance c') ts

    go _   (LitTy _)       = []
    go _   (CoercionTy _)  = []
    go pos (CastTy t _)    = go pos t

    goTyConApp _   Invariant     _ = []
    goTyConApp pos Bivariant     t = goTyConApp pos Contravariant t ++ goTyConApp pos Covariant t
    goTyConApp pos Covariant     t = go pos       t
    goTyConApp pos Contravariant t = go (not pos) t

    mutuallyRecursive tc tc' = tc `S.member` (dataConsOfTyCon tc')


dataConsOfTyCon :: TyCon -> S.HashSet TyCon
dataConsOfTyCon = dcs S.empty
  where
    dcs vis c                 = mconcat $ go vis <$> [irrelevantMult t | dc <- Ghc.tyConDataCons c, t <- Ghc.dataConOrigArgTys dc]
    go  vis (FunTy _ _ t1 t2) = go vis t1 `S.union` go vis t2
    go  vis (ForAllTy _ t)    = go vis t
    go  _   (TyVarTy _)       = S.empty
    go  vis (AppTy t1 t2)     = go vis t1 `S.union` go vis t2
    go  vis (TyConApp c ts)
      | c `S.member` vis
      = S.empty
      | otherwise
      = (S.insert c $ mconcat $ go vis <$> ts) `S.union` dcs (S.insert c vis) c
    go  _   (LitTy _)       = S.empty
    go  _   (CoercionTy _)  = S.empty
    go  vis (CastTy t _)    = go vis t

