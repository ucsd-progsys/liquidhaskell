
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
-- import Language.Haskell.Liquid.Misc (traceShow)
import Control.Exception (assert)
import Control.Applicative  ((<$>))   

import qualified Data.Map as M
import qualified Data.Set as S 
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
dropModuleNames s  = last $ words $ dotWhite <$> s 
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
 
