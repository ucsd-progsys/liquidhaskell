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

  -- * Resugar function
  , resugar
  ) where

import           CoreSyn
import           Name
import           PrelNames
import           Type
-- import           Var
-- import           Data.Maybe                                 (fromMaybe)

-- import           Debug.Trace

--------------------------------------------------------------------------------
-- | Data type for high-level patterns -----------------------------------------
--------------------------------------------------------------------------------

data Pattern
  = PatBindApp
      { patE1  :: !CoreExpr
      , patX   :: !Var
      , patE2  :: !CoreExpr
      , patM   :: !Type
      , patMDi :: !CoreExpr
      , patTyA :: !Type
      , patTyB :: !Type
      } -- ^ @e1 >>= \x -> e2@

resugar :: CoreExpr -> Maybe Pattern

resugar e
  | (Var v, [Type ty_m, _di, Type ty_a, Type ty_b, e1, Lam x e2])
      <- collectArgs e
  , getName v == bindMName
  = Just PatBindApp { patE1 = e1
                    , patX  = x
                    , patE2 = e2
                    , patM  = ty_m
                    , patMDi = _di
                    , patTyA = ty_a
                    , patTyB = ty_b
                    }

resugar _e = Nothing -- error "TODO:PATTERN"
