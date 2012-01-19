
{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}

module Language.Haskell.Liquid.GhcMisc2 where

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
import Type             (mkTyConTy, liftedTypeKind, substTyWith)
import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)



-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName initTyVarUnique occ noSrcSpan 
        occ  = mkTyVarOcc s

--stringRTyVar :: String -> RTyVar
--stringRTyVar = rTyVar . stringTyVar 


