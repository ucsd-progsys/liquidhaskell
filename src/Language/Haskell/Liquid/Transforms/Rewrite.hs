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
    rewriteBinds

  -- * Low-level Rewriting Function
  -- , rewriteWith

  -- * Rewrite Rule
  -- ,  RewriteRule

  ) where

import           CoreSyn
import           Type
import           TypeRep
import           TyCon
import           Var            (varType)
import qualified CoreSubst
import qualified Outputable
import           Data.Maybe     (fromMaybe)
import           Control.Monad  (msum)
import           Language.Haskell.Liquid.Misc (safeZipWithError, mapFst, mapSnd, mapThd3, Nat)
import           Language.Haskell.Liquid.GHC.Resugar
import           Language.Haskell.Liquid.GHC.Misc (isTupleId, tracePpr)
import           Language.Haskell.Liquid.UX.Config  (Config, simplifyCore)
-- import           Debug.Trace

--------------------------------------------------------------------------------
-- | Top-level rewriter --------------------------------------------------------
--------------------------------------------------------------------------------
rewriteBinds :: Config -> [CoreBind] -> [CoreBind]
rewriteBinds cfg
  | simplifyCore cfg = fmap (rewriteBindWith simplifyPatTuple)
  | otherwise        = id

--------------------------------------------------------------------------------
-- | A @RewriteRule@ is a function that maps a CoreExpr to another
--------------------------------------------------------------------------------
type RewriteRule = CoreExpr -> Maybe CoreExpr
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
rewriteBindWith :: RewriteRule -> CoreBind -> CoreBind
--------------------------------------------------------------------------------
rewriteBindWith r (NonRec x e) = NonRec x (rewriteWith r e)
rewriteBindWith r (Rec xes)    = Rec    (mapSnd (rewriteWith r) <$> xes)

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
    step e@(Type _)      = e
    step e@(Lit _)       = e
    step e@(Var _)       = e
    step e@(Coercion _)  = e


--------------------------------------------------------------------------------
-- | Rewriting Pattern-Match-Tuples --------------------------------------------
--------------------------------------------------------------------------------

{- [NOTE] The following is the structure of a @PatMatchTup@

      let x :: (t1,...,tn) = E[(x1,...,xn)]
          yn = case x of (..., yn) -> yn
          …
          y1 = case x of (y1, ...) -> y1
      in
          E'

  we strive to simplify the above to:

      E [ (x1,...,xn) := E' [y1 := x1,...,yn := xn] ]

  Need to rewrite

     (y1, ... , yn)

-}

--------------------------------------------------------------------------------
simplifyPatTuple :: RewriteRule
--------------------------------------------------------------------------------
simplifyPatTuple (Let (NonRec x e) rest)
  | Just (n, ts  ) <- varTuple x
  , 2 <= n
  , Just (yes, e') <- takeBinds n rest
  , let ys          = fst <$> yes
  , Just _         <- hasTuple (tracePpr "looking for tuple" ys) e
  , matchTypes yes ts
  = replaceTuple ys e e'

simplifyPatTuple _
  = Nothing

varTuple :: Var -> Maybe (Int, [Type])
varTuple x
  | TyConApp c ts <- varType x
  , isTupleTyCon c
  = Just (length ts, ts)
  | otherwise
  = Nothing

takeBinds  :: Nat -> CoreExpr -> Maybe ([(Var, CoreExpr)], CoreExpr)
takeBinds n e
  | n < 2     = Nothing
  | otherwise = {- tracePpr ("takeBinds " ++ show n)  -} mapFst reverse <$> go n e
    where
      -- vs      = map fst . fst <$> res
      go 0 e                      = Just ([], e)
      go n (Let (NonRec x e) e')  = do (xes, e'') <- go (n-1) e'
                                       Just ((x,e) : xes, e'')
      go _ _                      = Nothing

matchTypes :: [(Var, CoreExpr)] -> [Type] -> Bool
matchTypes xes ts =  xN == tN
                  && all (uncurry eqType) (safeZipWithError msg xts ts)
                  && all isProjection es
  where
    xN            = length xes
    tN            = length ts
    xts           = varType <$> xs
    (xs, es)      = unzip xes
    msg           = "RW:matchTypes"

isProjection :: CoreExpr -> Bool
isProjection e = case lift e of
                   Just (PatProject {}) -> True
                   _                    -> False

--------------------------------------------------------------------------------
-- | `hasTuple ys e` CHECKS if `e` contains a tuple that "looks like" (y1...yn)
--------------------------------------------------------------------------------
hasTuple :: [Var] -> CoreExpr -> Maybe [Var]
--------------------------------------------------------------------------------
hasTuple ys = stepE
  where
    stepE e
     | Just xs <- isVarTup ys e = Just xs
     | otherwise                = go e
    stepA (DEFAULT,_,_)         = Nothing
    stepA (_, _, e)             = stepE e
    go (Let _ e)                = stepE e
    go (Case _ _ _ cs)          = msum (stepA <$> cs)
    go _                        = Nothing

--------------------------------------------------------------------------------
-- | `replaceTuple ys e e'` REPLACES tuples that "looks like" (y1...yn) with e'
--------------------------------------------------------------------------------
replaceTuple :: [Var] -> CoreExpr -> CoreExpr -> Maybe CoreExpr
replaceTuple ys e e'            = stepE e
  where
    stepE e
     | Just xs <- isVarTup ys e = Just $ substTuple xs ys e'
     | otherwise                = go e
    stepA a@(DEFAULT,_,_)       = Just a
    stepA (c, xs, e)            = (c, xs,)   <$> stepE e
    go (Let b e)                = Let b      <$> stepE e
    go (Case e x t cs)          = Case e x t <$> mapM stepA cs
    go _                        = Nothing

--------------------------------------------------------------------------------
-- | `substTuple xs ys e'` returns e' [y1 := x1,...,yn := xn]
--------------------------------------------------------------------------------
substTuple :: [Var] -> [Var] -> CoreExpr -> CoreExpr
substTuple xs ys = CoreSubst.substExpr Outputable.empty (mkSubst ys xs)

mkSubst :: [Var] -> [Var] -> CoreSubst.Subst
mkSubst ys xs = CoreSubst.extendIdSubstList CoreSubst.emptySubst yxs
  where
    yxs       = safeZipWithError "RW:mkSubst" ys (Var <$> xs)

--------------------------------------------------------------------------------
-- | `isVarTup xs e` returns `Just ys` if e == (y1, ... , yn) and xi ~ yi
--------------------------------------------------------------------------------

isVarTup :: [Var] -> CoreExpr -> Maybe [Var]
isVarTup xs e
  | Just ys <- isTuple e
  , eqVars xs ys         = Just ys
isVarTup _ _             = Nothing

eqVars :: [Var] -> [Var] -> Bool
eqVars xs ys = {- F.tracepp ("eqVars: " ++ show xs' ++ show ys') -} xs' == ys'
  where
    xs' = {- F.symbol -} show <$> xs
    ys' = {- F.symbol -} show <$> ys

isTuple :: CoreExpr -> Maybe [Var]
isTuple e
  | (Var t, es) <- collectArgs e
  , isTupleId t
  , Just xs     <- mapM isVar (secondHalf es)
  = Just xs
  | otherwise
  = Nothing

isVar :: CoreExpr -> Maybe Var
isVar (Var x) = Just x
isVar _       = Nothing

secondHalf :: [a] -> [a]
secondHalf xs = drop (n `div` 2) xs
  where
    n         = length xs
