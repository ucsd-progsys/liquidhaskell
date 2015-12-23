{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.DataType (
    makeConTypes
  , makeTyConEmbeds

  , dataConSpec
  , meetDataConSpec
  ) where

import DataCon
import TyCon
import Var

import Control.Applicative ((<$>))
import Data.Maybe
import Data.Monoid

import qualified Data.List           as L
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar)
import Language.Fixpoint.Types (Symbol, TCEmb, meet)

import Language.Haskell.Liquid.GHC.Misc (symbolTyVar)
import Language.Haskell.Liquid.Types.PredType (dataConPSpecType)
import Language.Haskell.Liquid.Types.RefType (mkDataConIdsTy, ofType, rApp, rVar, uPVar)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc (mapSnd)
import Language.Haskell.Liquid.Types.Variance
import Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.OfType

-----------------------------------------------------------------------
-- Bare Predicate: DataCon Definitions --------------------------------
-----------------------------------------------------------------------

makeConTypes (name,spec) = inModule name $ makeConTypes' (Ms.dataDecls spec) (Ms.dvariance spec)

makeConTypes' :: [DataDecl] -> [(LocSymbol, [Variance])] -> BareM ([(TyCon, TyConP)], [[(DataCon, Located DataConP)]])
makeConTypes' dcs vdcs = unzip <$> mapM (uncurry ofBDataDecl) (group dcs vdcs)
  where
        group ds vs = merge (L.sort ds) (L.sortBy (\x y -> compare (fst x) (fst y)) vs)

        merge (d:ds) (v:vs)
          | tycName d == fst v = (Just d, Just v)  : merge ds vs
          | tycName d <  fst v = (Just d, Nothing) : merge ds (v:vs)
          | otherwise          = (Nothing, Just v) : merge (d:ds) vs
        merge []     vs  = ((Nothing,) . Just) <$> vs
        merge ds     []  = ((,Nothing) . Just) <$> ds



dataConSpec :: [(DataCon, DataConP)]-> [(Var, (RType RTyCon RTyVar RReft))]
dataConSpec dcs = concatMap mkDataConIdsTy [(dc, dataConPSpecType dc t) | (dc, t) <- dcs]

meetDataConSpec xts dcs  = M.toList $ L.foldl' upd dcm xts
  where
    dcm                  = M.fromList $ dataConSpec dcs
    upd dcm (x, t)       = M.insert x (maybe t (meet t) (M.lookup x dcm)) dcm

ofBDataDecl :: Maybe DataDecl  -> (Maybe (LocSymbol, [Variance])) -> BareM ((TyCon, TyConP), [(DataCon, Located DataConP)])
ofBDataDecl (Just (D tc as ps ls cts _ sfun)) maybe_invariance_info
  = do πs         <- mapM ofBPVar ps
       tc'        <- lookupGhcTyCon tc
       cts'       <- mapM (ofBDataCon lc lc' tc' αs ps ls πs) cts
       let tys     = [t | (_, dcp) <- cts', (_, t) <- tyArgs dcp]
       let initmap = zip (uPVar <$> πs) [0..]
       let varInfo = L.nub $  concatMap (getPsSig initmap True) tys
       let defaultPs = varSignToVariance varInfo <$> [0 .. (length πs - 1)]
       let (tvarinfo, pvarinfo) = f defaultPs
       return ((tc', TyConP αs πs ls tvarinfo pvarinfo sfun), (mapSnd (Loc lc lc') <$> cts'))
    where
       αs          = RTV . symbolTyVar <$> as
       n           = length αs
       lc          = loc  tc
       lc'         = locE tc
       f defaultPs = case maybe_invariance_info of
           {Nothing -> ([], defaultPs);
            Just (_,is) -> (take n is, if null (drop n is) then defaultPs else (drop n is))}


       varSignToVariance varsigns i = case filter (\p -> fst p == i) varsigns of
                                []       -> Invariant
                                [(_, b)] -> if b then Covariant else Contravariant
                                _        -> Bivariant

ofBDataDecl Nothing (Just (tc, is))
  = do tc'        <- lookupGhcTyCon tc
       return ((tc', TyConP [] [] [] tcov tcontr Nothing), [])
  where
    (tcov, tcontr) = (is, [])

ofBDataDecl Nothing Nothing
  = errorstar $ "Bare.DataType.ofBDataDecl called on invalid inputs"

getPsSig m pos (RAllT _ t)
  = getPsSig m pos t
getPsSig m pos (RApp _ ts rs r)
  = addps m pos r ++ concatMap (getPsSig m pos) ts
    ++ concatMap (getPsSigPs m pos) rs
getPsSig m pos (RVar _ r)
  = addps m pos r
getPsSig m pos (RAppTy t1 t2 r)
  = addps m pos r ++ getPsSig m pos t1 ++ getPsSig m pos t2
getPsSig m pos (RFun _ t1 t2 r)
  = addps m pos r ++ getPsSig m pos t2 ++ getPsSig m (not pos) t1
getPsSig m pos (RHole r)
  = addps m pos r
getPsSig _ _ z
  = error $ "getPsSig" ++ show z

getPsSigPs m pos (RProp _ (RHole r)) = addps m pos r
getPsSigPs m pos (RProp _ t) = getPsSig m pos t

addps m pos (MkUReft _ ps _) = (flip (,)) pos . f  <$> pvars ps
  where f = fromMaybe (error "Bare.addPs: notfound") . (`L.lookup` m) . uPVar

-- TODO:EFFECTS:ofBDataCon
ofBDataCon l l' tc αs ps ls πs (c, xts)
  = do c'      <- lookupGhcDataCon c
       ts'     <- mapM (mkSpecType' l ps) ts
       let cs   = map ofType (dataConStupidTheta c')
       let t0   = rApp tc rs (rPropP [] . pdVarReft <$> πs) mempty
       return   $ (c', DataConP l αs πs ls cs (reverse (zip xs ts')) t0 l')
    where
       (xs, ts) = unzip xts
       rs       = [rVar α | RTV α <- αs]


makeTyConEmbeds (mod, spec)
  = inModule mod $ makeTyConEmbeds' $ Ms.embeds spec

makeTyConEmbeds' :: TCEmb (Located Symbol) -> BareM (TCEmb TyCon)
makeTyConEmbeds' z = M.fromList <$> mapM tx (M.toList z)
  where
    tx (c, y) = (, y) <$> lookupGhcTyCon c
