{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Plugged (
    makePluggedSigs
  , makePluggedAsmSigs
  , makePluggedDataCons
  ) where

import DataCon
import Module
import Name
import NameSet
import TyCon
import Type (expandTypeSynonyms)
import Var

import Control.Applicative ((<$>), (<*>))
import Control.Monad
import Control.Monad.Error
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)
import Data.Monoid

import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Types.Names (dummySymbol)
import Language.Fixpoint.Types (mapPredReft, pAnd, conjuncts, TCEmb)
-- import Language.Fixpoint.Types (traceFix, showFix)

import Language.Haskell.Liquid.GHC.Misc (sourcePosSrcSpan)
import Language.Haskell.Liquid.Types.RefType (addTyConInfo, ofType, rVar, rTyVar, subts, toType, uReft)
import Language.Haskell.Liquid.Types

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Misc

makePluggedSigs name embs tcEnv exports sigs
  = forM sigs $ \(x,t) -> do
      let τ = expandTypeSynonyms $ varType x
      let r = maybeTrue x name exports
      (x,) <$> plugHoles embs tcEnv x r τ t

makePluggedAsmSigs embs tcEnv sigs
  = forM sigs $ \(x,t) -> do
      let τ = expandTypeSynonyms $ varType x
      let r = const killHoles
      (x,) <$> plugHoles embs tcEnv x r τ t

makePluggedDataCons embs tcEnv dcs
  = forM dcs $ \(dc, Loc l l' dcp) -> do
       let (das, _, dts, dt) = dataConSig dc
       tyArgs <- zipWithM (\t1 (x,t2) ->
                   (x,) . val <$> plugHoles embs tcEnv (dataConName dc) (const killHoles) t1 (Loc l l' t2))
                 dts (reverse $ tyArgs dcp)
       tyRes <- val <$> plugHoles embs tcEnv (dataConName dc) (const killHoles) dt (Loc l l' (tyRes dcp))
       return (dc, Loc l l' dcp { freeTyVars = map rTyVar das
                                , freePred   = map (subts (zip (freeTyVars dcp) (map (rVar :: TyVar -> RSort) das))) (freePred dcp)
                                , tyArgs     = reverse tyArgs
                                , tyRes      = tyRes})


plugHoles tce tyi x f t (Loc l l' st)
  = do tyvsmap <- case runMapTyVars (mapTyVars (toType rt') st'') initvmap of
                    Left e -> throwError e
                    Right s -> return $ vmap s
       let su    = [(y, rTyVar x) | (x, y) <- tyvsmap]
           st''' = subts su st''
           ps'   = fmap (subts su') <$> ps
           su'   = [(y, RVar (rTyVar x) ()) | (x, y) <- tyvsmap] :: [(RTyVar, RSort)]
       Loc l l' . mkArrow αs ps' (ls1 ++ ls2) [] . makeCls cs' <$> go rt' st'''
  where
    (αs, _, ls1, rt)  = bkUniv (ofType t :: SpecType)
    (cs, rt')         = bkClass rt

    (_, ps, ls2, st') = bkUniv st
    (_, st'')         = bkClass st'
    cs'               = [(dummySymbol, RApp c t [] mempty) | (c,t) <- cs]
    initvmap          = initMapSt $ ErrMismatch (sourcePosSrcSpan l) (pprint x) t (toType st)

    go :: SpecType -> SpecType -> BareM SpecType
    go t                (RHole r)          = return $ (addHoles t') { rt_reft = f t r }
      where
        t'       = everywhere (mkT $ addRefs tce tyi) t
        addHoles = everywhere (mkT $ addHole)
        -- NOTE: make sure we only add holes to RVar and RApp (NOT RFun)
        addHole :: SpecType -> SpecType
        addHole t@(RVar v r)       = RVar v (f t (uReft ("v", hole)))
        addHole t@(RApp c ts ps r) = RApp c ts ps (f t (uReft ("v", hole)))
        addHole t                  = t

    go (RVar _ _)       v@(RVar _ _)       = return v
    go (RFun _ i o _)   (RFun x i' o' r)   = RFun x <$> go i i' <*> go o o' <*> return r
    go (RAllT _ t)      (RAllT a t')       = RAllT a <$> go t t'
    go (RAllT a t)      t'                 = RAllT a <$> go t t'
    go t                (RAllP p t')       = RAllP p <$> go t t'
    go t                (RAllS s t')       = RAllS s <$> go t t'
    go t                (RAllE b a t')     = RAllE b a <$> go t t'
    go t                (REx b x t')       = REx b x <$> go t t'
    go t                (RRTy e r o t')    = RRTy e r o <$> go t t'
    go (RAppTy t1 t2 _) (RAppTy t1' t2' r) = RAppTy <$> go t1 t1' <*> go t2 t2' <*> return r
    go (RApp _ t _ _)   (RApp c t' p r)    = RApp c <$> (zipWithM go t t') <*> return p <*> return r
    -- If we reach the default case, there's probably an error, but we defer
    -- throwing it as checkGhcSpec does a much better job of reporting the
    -- problem to the user.
    go _                st                 = return st

    makeCls cs t              = foldr (uncurry rFun) t cs

addRefs :: TCEmb TyCon
     -> M.HashMap TyCon RTyCon
     -> SpecType
     -> SpecType
addRefs tce tyi (RApp c ts _ r) = RApp c' ts ps r
  where
    RApp c' _ ps _ = addTyConInfo tce tyi (RApp c ts [] r)
addRefs _ _ t  = t


maybeTrue :: NamedThing a => a -> ModName -> NameSet -> SpecType -> RReft -> RReft
maybeTrue x target exports t r
  | not (isFunTy t) && (isInternalName name || inTarget && notExported)
  = r
  | otherwise
  = killHoles r
  where
    inTarget    = moduleName (nameModule name) == getModName target
    name        = getName x
    notExported = not $ getName x `elemNameSet` exports

-- killHoles r@(U (Reft (v, rs)) _ _) = r { ur_reft = Reft (v, filter (not . isHole) rs) }

killHoles ur = ur { ur_reft = tx $ ur_reft ur }
  where
    tx r = {- traceFix ("killholes: r = " ++ showFix r) $ -} mapPredReft dropHoles r
    dropHoles    = pAnd . filter (not . isHole) . conjuncts
