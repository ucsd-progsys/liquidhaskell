{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains functions for "resugaring" low-level GHC `CoreExpr`
--   into high-level patterns, that can receive special case handling in
--   different phases (e.g. ANF, Constraint Generation, etc.)

module Language.Haskell.Liquid.GHC.Resugar (
  -- * High-level Source Patterns
    Pattern (..)

  -- * Lift a CoreExpr into a Pattern
  , lift

  -- * Lower a pattern back into a CoreExpr
  , lower
  ) where

import           CoreSyn
import           Type
import           PrelNames  (bindMName)
import           Name       (getName)
import qualified Data.List as L

-- import           Debug.Trace
-- import           Var
-- import           Data.Maybe                                 (fromMaybe)

--------------------------------------------------------------------------------
-- | Data type for high-level patterns -----------------------------------------
--------------------------------------------------------------------------------

data Pattern
  = PatBindApp
      { patE1  :: CoreExpr
      , patX   :: Var
      , patE2  :: CoreExpr
      , patM   :: Type
      , patMDi :: CoreExpr
      , patTyA :: Type
      , patTyB :: Type
      , patFF  :: Var
      }                      -- ^ e1 >>= \x -> e2

--------------------------------------------------------------------------------
-- | Lift expressions into High-level patterns ---------------------------------
--------------------------------------------------------------------------------
lift :: CoreExpr -> Maybe Pattern
--------------------------------------------------------------------------------
lift e = exprArgs e (collectArgs e)

--------------------------------------------------------------------------------
-- | Lower patterns back into expressions --------------------------------------
--------------------------------------------------------------------------------
lower :: Pattern -> CoreExpr
lower (PatBindApp e1 x e2 m d a b ff)
  = argsExpr (Var ff) [Type m, d, Type a, Type b, e1, Lam x e2]

argsExpr :: CoreExpr -> [CoreExpr] -> CoreExpr
argsExpr = L.foldl' App

exprArgs :: CoreExpr -> (CoreExpr, [CoreExpr]) -> Maybe Pattern
exprArgs _e (Var ff, [Type m, d, Type a, Type b, e1, Lam x e2])
  | isMonadicBind ff
  = Just (PatBindApp e1 x e2 m d a b ff)
exprArgs _ _
  = Nothing

isMonadicBind :: Var -> Bool
isMonadicBind v = getName v == bindMName
