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

import           DataCon      (DataCon)
import           CoreSyn
import           Type
import qualified MkCore
import qualified PrelNames as PN
import           Name         (Name, getName)
import qualified Data.List as L

-- import qualified Language.Haskell.Liquid.GHC.Misc as GM
-- import           Debug.Trace

--------------------------------------------------------------------------------
-- | Data type for high-level patterns -----------------------------------------
--------------------------------------------------------------------------------

data Pattern
  = PatBind
      { patE1  :: !CoreExpr
      , patX   :: !Var
      , patE2  :: !CoreExpr
      , patM   :: !Type
      , patDct :: !CoreExpr
      , patTyA :: !Type
      , patTyB :: !Type
      , patFF  :: !Var
      }                      -- ^ e1 >>= \x -> e2

  | PatReturn                -- return @ m @ t @ $dT @ e
     { patE    :: !CoreExpr  -- ^ e
     , patM    :: !Type      -- ^ m
     , patDct  :: !CoreExpr  -- ^ $dT
     , patTy   :: !Type      -- ^ t
     , patRet  :: !Var       -- ^ "return"
     }

  | PatProject               -- (case xe as x of C [x1,...,xn] -> xi) : ty
    { patXE    :: !Var       -- ^ xe
    , patX     :: !Var       -- ^ x
    , patTy    :: !Type      -- ^ ty
    , patCtor  :: !DataCon   -- ^ C
    , patBinds :: ![Var]     -- ^ [x1,...,xn]
    , patIdx   :: !Int       -- ^ i :: NatLT {len patBinds}
    }

  | PatSelfBind              -- let x = e in x
    { patX     :: !Var       -- ^ x
    , patE     :: !CoreExpr  -- ^ e
    }

  | PatSelfRecBind           -- letrec x = e in x
    { patX     :: !Var       -- ^ x
    , patE     :: !CoreExpr  -- ^ e
    }


_mbId :: CoreExpr -> Maybe Var
_mbId (Var x)    = Just x
_mbId (Tick _ e) = _mbId e
_mbId _          = Nothing

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

exprArgs (Case (Var xe) x t [(DataAlt c, ys, Var y)]) _
  | Just i <- y `L.elemIndex` ys
  = Just (PatProject xe x t c ys i)

{- TEMPORARILY DISBLED

exprArgs (Let (NonRec x e) e') _
  | Just y <- _mbId e', x == y
  = Just (PatSelfBind x e)

exprArgs (Let (Rec [(x, e)]) e') _
  | Just y <- _mbId e', x == y
  = Just (PatSelfRecBind x e)

-}
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
  = MkCore.mkCoreApps (Var op) [Type m, d, Type a, Type b, e1, Lam x e2]

lower (PatReturn e m d t op)
  = MkCore.mkCoreApps (Var op) [Type m, d, Type t, e]

lower (PatProject xe x t c ys i)
  = Case (Var xe) x t [(DataAlt c, ys, Var yi)] where yi = ys !! i

lower (PatSelfBind x e)
  = Let (NonRec x e) (Var x)

lower (PatSelfRecBind x e)
  = Let (Rec [(x, e)]) (Var x)
