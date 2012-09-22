
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections #-}

module GhcPlay where

import GHC		
import Outputable
import HscTypes 
import CoreSyn
import Type     (mkTyConTy)
import Var
import Name     (getSrcSpan)
import CoreMonad (liftIO)
import GHC.Paths (libdir)

import System.Environment (getArgs)
import DynFlags (defaultDynFlags)
import Serialized 
import Annotations 
import CorePrep
import VarEnv

import HscMain
import TypeRep
import TysPrim
import TysWiredIn
import DataCon 

--import HscMain  (hscTcRnLookupRdrName)
import TcRnDriver 
import RdrName
import OccName
import RnEnv
import TcRnMonad
import ErrUtils

------------------------------------------------------------------
-------------------- Type Checking Raw Strings -------------------
------------------------------------------------------------------

tcExpr ::  FilePath -> String -> IO Type
tcExpr f s = 
    runGhc (Just libdir) $ do
      df   <- getSessionDynFlags
      setSessionDynFlags df
      cm0  <- compileToCoreModule f
      setContext [(cm_module cm0)] []
      env  <- getSession
      r    <- liftIO $ hscTcExpr env s 
      return r

fileEnv f 
  = runGhc (Just libdir) $ do
      df    <- getSessionDynFlags
      setSessionDynFlags df
      cm0  <- compileToCoreModule f
      setContext [(cm_module cm0)] []
      env   <- getSession
      return env

stringNames env s 
  = do L _ rn          <- hscParseIdentifier env s
       (_, Just zs)    <- tcRnLookupRdrName env rn
       return zs

stringTyThing env s 
  = do L _ rn          <- hscParseIdentifier env s
       (_, Just (n:_)) <- tcRnLookupRdrName env rn
       (_, Just t)     <- tcRnLookupName env n
       return t 

{-

t0  <- stringTyThing env "Int"
t1  <- stringTyThing env "Con"
t2  <- stringTyThing env "L"
t3  <- stringTyThing env "sumTo"

intTyCon == tyThingTyCon t0
tyThingDataCon t1
showPpr $ tyThingTyCon t2
tyThingId t3

env  <- fileEnv "rangeAdt.hs"
n0s  <- stringNames env "Int" 
n1s  <- stringNames env "Con"
n1s  <- stringNames env "L"
n2s  <- stringNames env "sumTo"

-}
