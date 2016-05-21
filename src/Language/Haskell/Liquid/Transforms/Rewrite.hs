{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains functions for recursively "rewriting"
--   GHC core using "rules".

module Language.Haskell.Liquid.Transforms.Rewrite
  ( -- * Top level rewrite function
    rewrite

    -- * Low-level Rewriting Function
  , rewriteWith

  -- * Rewrite Rule
  ,  RewriteRule

  ) where

import           CoreUtils    (cheapEqExpr)
import           MkCore       (mkCoreVarTup)
import           CoreSyn
import           Type
import           TypeRep
import           TyCon
import           Var          (varType)
-- import qualified Data.List as L
import           Data.Maybe   (fromMaybe, isJust)
import           Language.Haskell.Liquid.Misc (mapSnd, mapThd3, Nat)
import           Language.Haskell.Liquid.GHC.Resugar
-- import           Debug.Trace


--------------------------------------------------------------------------------
-- | Top-level rewriter --------------------------------------------------------
--------------------------------------------------------------------------------
rewrite :: CoreExpr -> CoreExpr
rewrite = rewriteWith simplifyPatTuple

--------------------------------------------------------------------------------
-- | A @RewriteRule@ is a function that maps a CoreExpr to another
--------------------------------------------------------------------------------
type RewriteRule = CoreExpr -> Maybe CoreExpr
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
rewriteWith :: RewriteRule -> CoreExpr -> CoreExpr
--------------------------------------------------------------------------------
rewriteWith tx           = go
  where
    go                   = txTop . step
    txTop e              = fromMaybe e (tx e)
    goB (Rec xes)        = Rec         (mapSnd go <$> xes)
    goB (NonRec x e)     = NonRec x    (go e)
    step (Let b e)       = Let (goB b) (go e)
    step (App e e')      = App (go e)  (go e')
    step (Lam x e)       = Lam x       (go e)
    step (Cast e c)      = Cast (go e) c
    step (Tick t e)      = Tick t      (go e)
    step (Case e x t cs) = Case (go e) x t (mapThd3 go <$> cs)
    step e@(Lit _)       = e
    step e@(Var _)       = e
    step e@(Coercion _)  = e


--------------------------------------------------------------------------------
-- | Rewriting Pattern-Match-Tuples --------------------------------------------
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

--------------------------------------------------------------------------------
simplifyPatTuple :: RewriteRule
--------------------------------------------------------------------------------
simplifyPatTuple (Let (NonRec x e) rest)
  | Just (n, ts  ) <- varTuple x
  , Just (xes, e') <- takeBinds n rest
  , matchTypes xes ts
  , hasTuple xes e
  = substTuple e (fst <$> xes) e'

simplifyPatTuple _
  = Nothing
  -- = Just (PatMatchTup x n ts e (fst <$> xes) e')
  -- lower (PatMatchTup _ _ _ e xs e')

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

substTuple :: CoreExpr -> [Var] -> CoreExpr -> Maybe CoreExpr
substTuple e xs e' = searchReplace (tE, e') e
  where
    tE             = mkCoreVarTup xs

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
