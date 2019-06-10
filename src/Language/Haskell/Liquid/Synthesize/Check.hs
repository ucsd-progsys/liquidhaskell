{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module Language.Haskell.Liquid.Synthesize.Check (check) where


import Language.Fixpoint.Types.Constraints
import qualified Language.Fixpoint.Types.Config as F 
import qualified Language.Fixpoint.Types as F 
import Language.Fixpoint.Solver

import Language.Haskell.Liquid.Types.Types 
import Language.Haskell.Liquid.Types.Specs 
import Language.Haskell.Liquid.Constraint.Env 
import Language.Haskell.Liquid.Constraint.Generate 
import Language.Haskell.Liquid.Constraint.Types 
import Language.Haskell.Liquid.Constraint.ToFixpoint

import CoreSyn 
import Var 

check :: CGInfo -> CGEnv -> F.Config -> Var -> CoreExpr -> SpecType -> IO Bool 
check cgi γ cfg x e t = do 
    finfo <- cgInfoFInfo info' cs
    isSafe <$> solve cfg{F.srcFile = "SCheck" <> F.srcFile cfg} finfo 
  where 
    cs = generateConstraintsWithEnv info' cgi (γ{grtys = insertREnv (F.symbol x) t (grtys γ)}) 
    info' = info {giSrc = giSrc', giSpec = giSpec'}
    giSrc' = (giSrc info) {giCbs = [Rec [(x, e)]]}
    giSpec' = giSpecOld{gsSig = gsSig'}
    giSpecOld = giSpec info 
    gsSigOld  = gsSig giSpecOld
    gsSig' = gsSigOld {gsTySigs = (x,dummyLoc t):(gsTySigs gsSigOld)}
    info = ghcI cgi 



