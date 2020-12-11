{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams            #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Relational (consRelTop) where

#if !MIN_VERSION_base(4,14,0)
import Control.Monad.Fail
#endif

import           GHC.Stack
import           Language.Haskell.Liquid.GHC.API                   as Ghc hiding ( panic
                                                                                 , checkErr
                                                                                 , (<+>)
                                                                                 , text
                                                                                 , vcat
                                                                                 )
import           Language.Haskell.Liquid.GHC.TypeRep           ()
import           Text.PrettyPrint.HughesPJ hiding ((<>)) 
import           Control.Monad.State
import           Data.Maybe                                    (fromMaybe, catMaybes, isJust)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import qualified Data.Foldable                                 as F
import qualified Data.Traversable                              as T
import qualified Data.Functor.Identity
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Visitor
import qualified Language.Fixpoint.Types                       as F
import qualified Language.Fixpoint.Types.Visitor               as F
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Init
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Monad
import           Language.Haskell.Liquid.Constraint.Split
import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.GHC.Play          (isHoleVar) 
import qualified Language.Haskell.Liquid.GHC.Resugar           as Rs
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
import qualified Language.Haskell.Liquid.GHC.Misc         as GM -- ( isInternal, collectArguments, tickSrcSpan, showPpr )
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Constraint
import           Language.Haskell.Liquid.Transforms.Rec
import           Language.Haskell.Liquid.Transforms.CoreToLogic (weakenResult)
import           Language.Haskell.Liquid.Bare.DataType (makeDataConChecker)

import           Language.Haskell.Liquid.Types hiding (binds, Loc, loc, Def)


consRelTop :: Config -> TargetInfo -> CGEnv  
          -> (Var, Var, LocSpecType, LocSpecType, F.Expr) -> CG ()
consRelTop _ ti γ (x,y,t,s,p) = do 
  let cbs = giCbs $ giSrc ti 
  let e = findBody x cbs
  let d = findBody y cbs
  let e' = F.tracepp ("To CHECK " ++ show (e,d,t,s,p)) e
  consRel γ [] e' d (val t) (val s) p 

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRel :: CGEnv -> [F.Expr] 
        -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> F.Expr -> CG ()
consRel γ ψ (Tick _ e) d t s p = 
  consRel γ ψ e d t s p 

consRel γ ψ e (Tick _ d) t s p = 
  consRel γ ψ e d t s p 

consRel γ ψ (Lam x e) (Lam y d) (RFun _ _ t _) (RFun _ _ s _) p = 
  consRel γ ψ e d t s p 

consRel γ ψ (Let _ e) (Let _ d) t s p = 
  consRel γ ψ e d t s p 

consRel γ ψ e@(Var _) d@(Var _) t s p = 
  return $ F.tracepp ("To CHECK " ++ show (e,d,t,s,p)) ()

consRel γ ψ e@(Lit _) d@(Lit _) t s p = 
  return $ F.tracepp ("To CHECK " ++ show (e,d,t,s,p)) ()

consRel γ ψ e d t s p = 
  error ("define me!" ++ show (e,d,t,s,p))

--------------------------------------------------------------
-- Helper Definitions ---------------------------------------- 
--------------------------------------------------------------

findBody :: Var -> [CoreBind] -> CoreExpr 
findBody x bs = case lookup x (concatMap binds bs) of 
                 Nothing -> error ("Not found definition for " ++ show x)
                 Just e  -> e
  where 
    binds (NonRec x e) = [(x,e)]
    binds (Rec xes)    = xes 
  