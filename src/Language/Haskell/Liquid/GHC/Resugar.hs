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
import           Type
import           PrelNames  (bindMName)
import           Name       (getName)

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
      }                      -- ^ e1 >>= \x -> e2

--------------------------------------------------------------------------------
-- | API for detecting special patterns ----------------------------------------
--------------------------------------------------------------------------------
resugar :: CoreExpr -> Maybe Pattern
--------------------------------------------------------------------------------
resugar e = resugarEArgs e (collectArgs e)


resugarEArgs :: CoreExpr -> (CoreExpr, [CoreExpr]) -> Maybe Pattern
resugarEArgs _e (Var ff, [Type m, d, Type a, Type b, e1, Lam x e2])
  | isMonadicBind ff
  = Just (PatBindApp e1 x e2 m d a b)
resugarEArgs _ _
  = Nothing

isMonadicBind :: Var -> Bool
isMonadicBind v = getName v == bindMName
