
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

dropModuleNames = last . words . (dotWhite `fmap`) 
  where dotWhite '.' = ' '
        dotWhite c   = c

--dropModuleNames x =  x -- (mylast x (words (dotWhite <$> x)))
--  where dotWhite '.' = ' '
--        dotWhite c   = c
--
--mylast x [] = error $ "RefType.last" ++ showPpr x
--mylast x l  = last l
