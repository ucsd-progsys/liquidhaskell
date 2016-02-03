
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
{-# LANGUAGE PartialTypeSignatures     #-}

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
  , localBindsOfType
  , lookupREnv
  , (?=)

  -- * Pruning refinements (TODO: move!)
 , rTypeSortedReft'

  -- * Extend CGEnv
 , setLocation, setBind, setRecs, setTRec

  -- * Lookup CGEnv
 , getLocation

) where


-- import Name (getSrcSpan)
import Prelude hiding (error)
import CoreSyn (CoreExpr)
import SrcLoc
import Var
-- import Outputable
-- import FastString (fsLit)
import Control.Monad.State
import Control.Monad (msum)

-- import           GHC.Err.Located hiding (error)
import           GHC.Stack

import           Control.Arrow           (first)
import           Data.Maybe              -- (fromMaybe)
import qualified Data.List               as L
import qualified Data.HashSet            as S
import qualified Data.HashMap.Strict     as M
import qualified Language.Fixpoint.Types as F

import           Language.Fixpoint.Misc hiding (errorstar)
import           Language.Fixpoint.SortCheck (pruneUnsortedReft)

import           Language.Haskell.Liquid.Misc (firstJust)
import           Language.Haskell.Liquid.GHC.Misc (tickSrcSpan)
import           Language.Haskell.Liquid.Types.RefType
import qualified Language.Haskell.Liquid.GHC.SpanStack as Sp
import           Language.Haskell.Liquid.Types            hiding (binds, Loc, loc, freeTyVars, Def)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Transforms.RefSplit
import qualified Language.Haskell.Liquid.UX.CTags       as Tg

instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

--------------------------------------------------------------------------------
-- | Refinement Type Environments ----------------------------------------------
--------------------------------------------------------------------------------

-- updREnvLocal :: REnv -> (_ -> _) -> REnv
updREnvLocal rE f      = rE { reLocal = f (reLocal rE) }

-- RJ: REnv-Split-Bug?
filterREnv :: (SpecType -> Bool) -> REnv -> REnv
filterREnv f rE        = rE `updREnvLocal` (M.filter f)

fromListREnv :: [(F.Symbol, SpecType)] -> [(F.Symbol, SpecType)] -> REnv
fromListREnv gXts lXts = REnv (M.fromList gXts) (M.fromList lXts)

-- RJ: REnv-Split-Bug?
deleteREnv :: F.Symbol -> REnv -> REnv
deleteREnv x rE = rE `updREnvLocal` (M.delete x)

insertREnv :: F.Symbol -> SpecType -> REnv -> REnv
insertREnv x y rE = rE `updREnvLocal` (M.insert x y)

lookupREnv :: F.Symbol -> REnv -> Maybe SpecType
lookupREnv x rE = msum $ M.lookup x <$> renvMaps rE

memberREnv :: F.Symbol -> REnv -> Bool
memberREnv x rE = or   $ M.member x <$> renvMaps rE

renvMaps rE = [reLocal rE, reGlobal rE]

--------------------------------------------------------------------------------
localBindsOfType :: RRType r  -> CGEnv -> [F.Symbol]
--------------------------------------------------------------------------------
localBindsOfType tx γ = fst <$> toListREnv (filterREnv ((== toRSort tx) . toRSort) (renv γ))

-- RJ: REnv-Split-Bug?
toListREnv :: REnv -> [(F.Symbol, SpecType)]
toListREnv = M.toList . reLocal


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

addBinders :: CGEnv -> F.Symbol -> [(F.Symbol, SpecType)] -> CG CGEnv
addBinders γ0 x' cbs   = foldM (++=) (γ0 -= x') [("addBinders", x, t) | (x, t) <- cbs]

addBind :: SrcSpan -> F.Symbol -> F.SortedReft -> CG ((F.Symbol, F.Sort), F.BindId)
addBind l x r = do
  st          <- get
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
    xs            = localBindsOfType tyy γ
    t             = L.foldl' F.meet ttrue [ tyx' `F.subst1` (yy, F.EVar x) | x <- xs]
    (tyx', ttrue) = splitXRelatedRefs yy tyx

addCGEnv tx γ (_, x, t') = do
  idx   <- fresh
  let t  = tx $ normalize idx t'
  let l  = getLocation γ
  let γ' = γ { renv = insertREnv x t (renv γ) }
  pflag <- pruneRefs <$> get
  is    <- if isBase t
             then (:) <$> addBind l x (rTypeSortedReft' pflag γ' t) <*> addClassBind l t
             else return []
  return $ γ' { fenv = insertsFEnv (fenv γ) is }

rTypeSortedReft' pflag γ
  | pflag     = pruneUnsortedReft (feEnv $ fenv γ) . f
  | otherwise = f
  where
    f         = rTypeSortedReft (emb γ)

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
  where err = panic Nothing $ msg ++ " Duplicate binding for "
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
γ ?= x  = lookupREnv x (renv γ)

------------------------------------------------------------------------
setLocation :: CGEnv -> Sp.Span -> CGEnv
------------------------------------------------------------------------
setLocation γ p = γ { cgLoc = Sp.push p $ cgLoc γ }

------------------------------------------------------------------------
setBind :: CGEnv -> Var -> CGEnv
------------------------------------------------------------------------
setBind γ x = γ `setLocation` Sp.Var x `setBind'` x

setBind' :: CGEnv -> Tg.TagKey -> CGEnv
setBind' γ k
  | Tg.memTagEnv k (tgEnv γ) = γ { tgKey = Just k }
  | otherwise                = γ

------------------------------------------------------------------------
setRecs :: CGEnv -> [Var] -> CGEnv
------------------------------------------------------------------------
setRecs γ xs   = γ { recs = L.foldl' (flip S.insert) (recs γ) xs }

------------------------------------------------------------------------
setTRec :: CGEnv -> [(Var, SpecType)] -> CGEnv
------------------------------------------------------------------------
setTRec γ xts  = γ' {trec = Just $ M.fromList xts' `M.union` trec'}
  where
    γ'         = γ `setRecs` (fst <$> xts)
    trec'      = fromMaybe M.empty $ trec γ
    xts'       = first F.symbol <$> xts

------------------------------------------------------------------------
getLocation :: CGEnv -> SrcSpan
------------------------------------------------------------------------
getLocation = Sp.srcSpan . cgLoc
