
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

-- | This module defines the representation for Environments needed
--   during constraint generation.

module Language.Haskell.Liquid.Constraint.Env (

  -- * Insert
    (+++=)
  , (++=)
  , (+=)
  , extendEnvWithVV
  , addBinders
  , addSEnv
  , (-=)

  -- * Construction
  , fromListREnv

  -- * Query
  , bindsOfType
  , lookupREnv
  , (?=)

  -- * Pruning refinements (TODO: move!)
 , rTypeSortedReft'
) where

import CoreSyn (CoreExpr)
import SrcLoc  (SrcSpan)
import Control.Monad.State


import GHC.Err.Located hiding (error)
import GHC.Stack

import Data.Maybe               (fromMaybe)
import qualified Data.HashMap.Strict                as M
import qualified Language.Fixpoint.Types            as F
import Language.Fixpoint.Misc

import Language.Fixpoint.SortCheck (pruneUnsortedReft)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types            hiding (binds, Loc, loc, freeTyVars, Def)
import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Constraint.Fresh
import Language.Haskell.Liquid.Transforms.RefSplit


instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

--------------------------------------------------------------------------------
-- | Refinement Type Environments ----------------------------------------------
--------------------------------------------------------------------------------

toListREnv (REnv env)     = M.toList env
filterREnv f (REnv env)   = REnv $ M.filter f env
fromListREnv              = REnv . M.fromList
deleteREnv x (REnv env)   = REnv (M.delete x env)
insertREnv x y (REnv env) = REnv (M.insert x y env)
lookupREnv x (REnv env)   = M.lookup x env
memberREnv x (REnv env)   = M.member x env

--------------------------------------------------------------------------------
bindsOfType :: RRType r  -> CGEnv -> [F.Symbol]
--------------------------------------------------------------------------------
bindsOfType tx γ = fst <$> toListREnv (filterREnv ((== toRSort tx) . toRSort) (renv γ))


--------------------------------------------------------------------------------
extendEnvWithVV :: CGEnv -> SpecType -> CG CGEnv
--------------------------------------------------------------------------------
extendEnvWithVV γ t
  | F.isNontrivialVV vv && not (vv `memberREnv` (renv γ))
  = (γ, "extVV") += (vv, t)
  | otherwise
  = return γ
  where
    vv = rTypeValueVar t


addBinders γ0 x' cbs   = foldM (++=) (γ0 -= x') [("addBinders", x, t) | (x, t) <- cbs]

addBind :: SrcSpan -> F.Symbol -> F.SortedReft -> CG ((F.Symbol, F.Sort), F.BindId)
addBind l x r
  = do st          <- get
       let (i, bs') = F.insertBindEnv x r (binds st)
       put          $ st { binds = bs' } { bindSpans = M.insert i l (bindSpans st) }
       return ((x, F.sr_sort r), i) -- traceShow ("addBind: " ++ showpp x) i

addClassBind :: SrcSpan -> SpecType -> CG [((F.Symbol, F.Sort), F.BindId)]
addClassBind l = mapM (uncurry (addBind l)) . classBinds



{- see tests/pos/polyfun for why you need everything in fixenv -}
addCGEnv :: (SpecType -> SpecType) -> CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
addCGEnv tx γ (msg, x, REx y tyy tyx)
  = do y' <- fresh
       γ' <- addCGEnv tx γ (msg, y', tyy)
       addCGEnv tx γ' (msg, x, tyx `F.subst1` (y, F.EVar y'))

addCGEnv tx γ (msg, x, RAllE yy tyy tyx)
  = addCGEnv tx γ (msg, x, t)
  where
    xs    = bindsOfType tyy γ
    t     = foldl F.meet ttrue [ tyx' `F.subst1` (yy, F.EVar x) | x <- xs]

    (tyx', ttrue) = splitXRelatedRefs yy tyx

addCGEnv tx γ (_, x, t')
  = do idx   <- fresh
       let t  = tx $ normalize idx t'
       let l  = loc γ
       let γ' = γ { renv = insertREnv x t (renv γ) }
       pflag <- pruneRefs <$> get
       is    <- if isBase t
                  then (:) <$> addBind l x (rTypeSortedReft' pflag γ' t) <*> addClassBind l t
                  else return []
       return $ γ' { fenv = insertsFEnv (fenv γ) is }

rTypeSortedReft' pflag γ
  | pflag
  = pruneUnsortedReft (fe_env $ fenv γ) . f
  | otherwise
  = f
  where
    f = rTypeSortedReft (emb γ)

normalize idx = normalizeVV idx . normalizePds

normalizeVV idx t@(RApp _ _ _ _)
  | not (F.isNontrivialVV (rTypeValueVar t))
  = shiftVV t (F.vv $ Just idx)

normalizeVV _ t
  = t


--------------------------------------------------------------------------------
(+=) :: (CGEnv, String) -> (F.Symbol, SpecType) -> CG CGEnv
--------------------------------------------------------------------------------
(γ, msg) += (x, r)
  | x == F.dummySymbol
  = return γ
  | x `memberREnv` (renv γ)
  = err
  | otherwise
  =  γ ++= (msg, x, r)
  where err = errorstar $ msg ++ " Duplicate binding for "
                              ++ F.symbolString x
                              ++ "\n New: " ++ showpp r
                              ++ "\n Old: " ++ showpp (x `lookupREnv` (renv γ))


--------------------------------------------------------------------------------
(++=) :: CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
--------------------------------------------------------------------------------
(++=) γ = addCGEnv (addRTyConInv (M.unionWith mappend (invs γ) (ial γ))) γ

--------------------------------------------------------------------------------
addSEnv :: CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
--------------------------------------------------------------------------------
addSEnv γ = addCGEnv (addRTyConInv (invs γ)) γ

(+++=) :: (CGEnv, String) -> (F.Symbol, CoreExpr, SpecType) -> CG CGEnv
(γ, _) +++= (x, e, t) = (γ{lcb = M.insert x e (lcb γ)}, "+++=") += (x, t)

γ -= x =  γ {renv = deleteREnv x (renv γ), lcb  = M.delete x (lcb γ)}

(?=) :: (?callStack :: CallStack) => CGEnv -> F.Symbol -> Maybe SpecType
γ ?= x  = {- fromMaybe (errorstar msg) $ -} lookupREnv x (renv γ)
  -- where
    -- msg = "EnvLookup:: unknown binder " ++ showpp x
                               -- ++ " in renv\n"
                               -- ++ showpp (renv γ)

--------------------------------------------------------------------------------
-- lookupEnv :: (?callStack :: CallStack) => CGEnv -> F.Symbol -> Maybe SpecType
--------------------------------------------------------------------------------
-- lookupEnv γ x = lookupREnv x (renv γ)
