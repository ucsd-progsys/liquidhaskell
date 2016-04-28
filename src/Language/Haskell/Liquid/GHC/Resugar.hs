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
import qualified PrelNames as PN -- (bindMName)
import           Name       (Name, getName)
import qualified Data.List as L

-- import           Debug.Trace
-- import           Var
-- import           Data.Maybe                                 (fromMaybe)

--------------------------------------------------------------------------------
-- | Data type for high-level patterns -----------------------------------------
--------------------------------------------------------------------------------

data Pattern
  = PatBind
      { patE1  :: CoreExpr
      , patX   :: Var
      , patE2  :: CoreExpr
      , patM   :: Type
      , patDct :: CoreExpr
      , patTyA :: Type
      , patTyB :: Type
      , patFF  :: Var
      }                      -- ^ e1 >>= \x -> e2

  | PatReturn
     { patE    :: CoreExpr
     , patM    :: Type
     , patDct  :: CoreExpr
     , patTy   :: Type
     , patRet  :: Var
     }                       -- ^ return e

--------------------------------------------------------------------------------
-- | Lift expressions into High-level patterns ---------------------------------
--------------------------------------------------------------------------------
lift :: CoreExpr -> Maybe Pattern
--------------------------------------------------------------------------------
lift e = exprArgs e (collectArgs e)

exprArgs :: CoreExpr -> (CoreExpr, [CoreExpr]) -> Maybe Pattern
exprArgs _e (Var op, [Type m, d, Type a, Type b, e1, Lam x e2])
  | op `is` PN.bindMName
  = Just (PatBind e1 x e2 m d a b op)

exprArgs _e (Var op, [Type m, d, Type t, e])
  | op `is` PN.returnMName
  = Just (PatReturn e m d t op)

exprArgs _ _
  = Nothing

is :: Var -> Name -> Bool
is v n = n == getName v

--------------------------------------------------------------------------------
-- | Lower patterns back into expressions --------------------------------------
--------------------------------------------------------------------------------
lower :: Pattern -> CoreExpr
--------------------------------------------------------------------------------

lower (PatBind e1 x e2 m d a b op)
  = argsExpr (Var op) [Type m, d, Type a, Type b, e1, Lam x e2]

lower (PatReturn e m d t op)
  = argsExpr (Var op) [Type m, d, Type t, e]

argsExpr :: CoreExpr -> [CoreExpr] -> CoreExpr
argsExpr = L.foldl' App
