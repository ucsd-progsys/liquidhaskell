
{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}

module Language.Haskell.Liquid.GhcMisc where

import GHC
import Outputable
import qualified TyCon as TC
import DataCon
import TypeRep 
import Var
import VarEnv
import PrelNames
import Name             (getSrcSpan, getOccString, mkInternalName)
import OccName          (mkTyVarOcc)
import Unique           (getKey, getUnique, initTyVarUnique)
import Literal
import Type             (mkTyConTy, liftedTypeKind, eqType, substTyWith)
import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)
import CoreSyn          
import CostCentre 
import HscTypes         (ModGuts(..), Dependencies, ImportedMods)
import RdrName          (GlobalRdrEnv)
import FamInstEnv       (FamInst)

import Language.Haskell.Liquid.Misc (stripParens)
import Control.Exception (assert)
import Control.Applicative  ((<$>))   

import qualified Data.Map as M
import qualified Data.Set as S 

-----------------------------------------------------------------------
--------------- Datatype For Holding GHC ModGuts ----------------------
-----------------------------------------------------------------------

data MGIModGuts = MI { 
    mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module 
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: !ImportedMods
  , mgi_rdr_env   :: !GlobalRdrEnv
  , mgi_tcs       :: ![TyCon]
  , mgi_fam_insts :: ![FamInst]
  }

miModGuts mg = MI { 
    mgi_binds     = mg_binds mg 
  , mgi_module    = mg_module mg
  , mgi_deps      = mg_deps mg
  , mgi_dir_imps  = mg_dir_imps mg
  , mgi_rdr_env   = mg_rdr_env mg
  , mgi_tcs       = mg_tcs mg
  , mgi_fam_insts = mg_fam_insts mg
  }

-----------------------------------------------------------------------
--------------- Generic Helpers for Encoding Location -----------------
-----------------------------------------------------------------------

srcSpanTick :: Module -> SrcSpan -> Tickish a 
srcSpanTick m loc 
  = ProfNote (AllCafsCC m loc) False True

tickSrcSpan :: Tickish a -> SrcSpan
tickSrcSpan (ProfNote (AllCafsCC _ loc) _ _) 
  = loc 

-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName initTyVarUnique occ noSrcSpan 
        occ  = mkTyVarOcc s
 
tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} show α ++ show (varUnique α)
  
intersperse d ds = hsep $ punctuate (space <> d) ds

tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) $ x

pprShow = text . show 

dropModuleNames [] = [] 
dropModuleNames s  = last $ words $ dotWhite <$> stripParens s 
  where dotWhite '.' = ' '
        dotWhite c   = c

--dropModuleNames x =  x -- (mylast x (words (dotWhite <$> x)))
--  where dotWhite '.' = ' '
--        dotWhite c   = c
--
--mylast x [] = error $ "RefType.last" ++ showPpr x
--mylast x l  = last l


--instance Outputable a => Outputable (S.Set a) where
--  ppr = ppr . S.toList 
-- 
--instance (Outputable k, Outputable v) => Outputable (M.Map k v) where
--  ppr = ppr . M.toList 
 
