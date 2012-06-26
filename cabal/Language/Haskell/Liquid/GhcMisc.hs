
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
import Language.Haskell.Liquid.Misc (traceShow)
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

--eqTv α α' = traceShow msg $ assert (res == eqTv' α α') $ res  
--  where res = eqType (TyVarTy α) (TyVarTy α')
--        msg = "eqTv: α = " ++ tvId α ++ " α' = " ++ tvId α' 
--eqTv α α' = traceShow msg $ tvId α == tvId α'
--  where msg = "eqTv: α = " ++ tvId α ++ " α' = " ++ tvId α' 
 
tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} show α ++ show (varUnique α)
  



