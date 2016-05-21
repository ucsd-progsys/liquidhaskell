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

module Language.Haskell.Liquid.Transforms.TupleMatch ( simplify ) where

import           CoreUtils    (cheapEqExpr)
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
import           Data.Maybe   (fromMaybe, isJust)
import           Language.Haskell.Liquid.Misc (Nat)
-- import           Debug.Trace

--------------------------------------------------------------------------------
simplify :: CoreExpr -> CoreExpr
--------------------------------------------------------------------------------
simplify = error "TBD:TupleMatch:simplify"

simplify (Let (NonRec x e) rest) =
  | Just (n, ts  ) <- varTuple x
  , Just (xes, e') <- takeBinds n rest
  , matchTypes xes ts
  , hasTuple xes e
  = Just (PatMatchTup x n ts e (fst <$> xes) e')

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

takeBinds  :: Nat -> CoreExpr -> Maybe ([(Var, CoreExpr)], CoreExpr)
takeBinds 0 e
  = Just ([], e)
takeBinds n (Let (NonRec x e) e')
  = do (xes, e'') <- takeBinds (n-1) e'
       Just ((x,e):xes, e'')
takeBinds _ _
  = Nothing

matchTypes :: [(Var, CoreExpr)] -> [Type] -> Bool
matchTypes xes ts =  xN == tN
                  && all (uncurry eqType) (zip xts ts)
                  && all isProjection es
  where
    xN            = length xes
    tN            = length ts
    xts           = varType <$> xs
    (xs, es)      = unzip xes

isProjection :: CoreExpr -> Bool
isProjection e = case lift e of
                   Just (PatProject {}) -> True
                   _                    -> False

hasTuple   :: [(Var, a)] -> CoreExpr -> Bool
hasTuple xes = isSubExpr tE
  where
    tE       = mkCoreVarTup (fst <$> xes)

-- HARD
substTuple :: CoreExpr -> [Var] -> CoreExpr -> CoreExpr
substTuple e xs e' = fromMaybe e $ searchReplace (tE, e') e
  where
    tE             = mkCoreVarTup xs

-- HARD
isSubExpr :: CoreExpr -> CoreExpr -> Bool
isSubExpr inE outE = isJust $ searchReplace (inE, inE) outE

searchReplace :: (CoreExpr, CoreExpr) -> CoreExpr -> Maybe CoreExpr
searchReplace (iE, oE)     = stepE
  where
    stepE e                = if cheapEqExpr e iE then Just oE else go e
    stepA (c, xs, e)       = (c, xs,)   <$> stepE e
    stepA a@(DEFAULT,_,_)  = Just a
    go (Let b e)           = Let b      <$> stepE e
    go (Case e x t cs)     = Case e x t <$> mapM stepA cs
    go _                   = Nothing

    -- go' (Rec xes)      = undefined
    -- go' (NonRec x e)   = undefined
    -- go (App e1 e2)     = undefined
    -- go (Lam x e)       = undefined
    -- go (Cast e c)      = undefined
    -- go (Tick t e)      = undefined


varTuple :: Var -> Maybe (Int, [Type])
varTuple x
  | TyConApp c ts <- varType x
  , isTupleTyCon c
  = Just (length ts, ts)
  | otherwise
  = Nothing
