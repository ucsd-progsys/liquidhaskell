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
import           MkCore       (mkCoreApps, mkCoreVarTup)
import           CoreSyn
import           Type
import           TypeRep
import           TyCon
import qualified PrelNames as PN -- (bindMName)
import           Name         (Name, getName)
import           Var          (varType)
import qualified Data.List as L
-- import           Debug.Trace
-- import           Var
-- import           Data.Maybe                                 (fromMaybe)

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
     , patDct  :: !CoreExpr  -- $ $dT
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

 | PatMatchTup               -- See NOTE on @PatMatchTup@
    { patX    :: !Var
    , patN    :: !Int
    , patTs   :: ![Type]    -- ListN Type patN
    , patE    :: !CoreExpr
    , patXs   :: ![Var]     -- ListN Var patN
    , patE'   :: CoreExpr
    }


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

exprArgs (Let (NonRec x e) rest) _
  | Just (n, ts  ) <- varTuple x
  , Just (xes, e') <- takeBinds n rest
  , matchTypes xes ts
  , hasTuple xes e
  = Just (PatMatchTup x n ts e (fst <$> xes) e')

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
  = mkCoreApps (Var op) [Type m, d, Type a, Type b, e1, Lam x e2]

lower (PatReturn e m d t op)
  = mkCoreApps (Var op) [Type m, d, Type t, e]

lower (PatProject xe x t c ys i)
  = Case (Var xe) x t [(DataAlt c, ys, Var yi)] where yi = ys !! i

lower (PatMatchTup _ _ _ e xs e')
  = substTuple e xs e'

--------------------------------------------------------------------------------
-- | Pattern-Match-Tuples ------------------------------------------------------
--------------------------------------------------------------------------------

{- [NOTE] The following is the structure of a @PatMatchTup@

      let x :: (t1,...,tn) = E[(x1,...,xn)]
          xn = case x of (..., yn) -> yn
          …
          x1 = case x of (y1, ...) -> y1
      in
          E'

  we strive to simplify the above to:

      E [ (x1,...,xn) := E' ]
-}

{- Ooh, some helpful things!

  mkCoreTup

-}

substTuple :: CoreExpr -> [Var] -> CoreExpr -> CoreExpr
substTuple = error "TBD:substTuple"

takeBinds  :: Int -> CoreExpr -> Maybe ([(Var, CoreExpr)], CoreExpr)
takeBinds = error "TBD:takeBinds"

matchTypes :: [(Var, CoreExpr)] -> [Type] -> Bool
matchTypes xes ts =  xN == tN
                  && all (uncurry eqType) (zip xts ts)
                  && all isProjection es
  where
    xN       = length xes
    tN       = length ts
    xts      = varType <$> xs
    (xs, es) = unzip xes

isProjection :: CoreExpr -> Bool
isProjection = error "TBD:isProjection"



hasTuple   :: [(Var, a)] -> CoreExpr -> Bool
hasTuple xes = isSubExpr tE
  where
    tE       = mkCoreVarTup (fst <$> xes)

isSubExpr :: CoreExpr -> CoreExpr -> Bool
isSubExpr = error "TBD:isSubExpr"


varTuple :: Var -> Maybe (Int, [Type])
varTuple x
  | TyConApp c ts <- varType x
  , isTupleTyCon c
  = Just (length ts, ts)
  | otherwise
  = Nothing
