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
import qualified CoreSubst
import qualified Outputable
import qualified CoreUtils
-- import qualified PrelNames
import qualified Var
import qualified MkCore
import           Data.Maybe     (fromMaybe)
import           Control.Monad  (msum)
-- import qualified Data.List as L
-- import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Misc       (mapFst, mapSnd)

import           Language.Haskell.Liquid.Misc (safeZipWithError, mapThd3, Nat)
import           Language.Haskell.Liquid.GHC.Resugar
import           Language.Haskell.Liquid.GHC.Misc (isTupleId) -- showPpr, tracePpr, isTupleId)
import           Language.Haskell.Liquid.UX.Config  (Config, noSimplifyCore)
-- import           Debug.Trace

--------------------------------------------------------------------------------
-- | Top-level rewriter --------------------------------------------------------
--------------------------------------------------------------------------------
rewriteBinds :: Config -> [CoreBind] -> [CoreBind]
rewriteBinds cfg
  | simplifyCore cfg = fmap (rewriteBindWith simplifyPatTuple)
  | otherwise        = id

simplifyCore :: Config -> Bool
simplifyCore = not . noSimplifyCore

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

{-
    let CrazyPat x1 ... xn = e in e'

    let t : (t1,...,tn) = "CrazyPat e ... (y1, ..., yn)"
        xn = Proj t n
        ...
        x1 = Proj t 1
    in
        e'

    "crazy-pat"
 -}

{- [NOTE] The following is the structure of a @PatMatchTup@

      let x :: (t1,...,tn) = E[(x1,...,xn)]
          yn = case x of (..., yn) -> yn
          …
          y1 = case x of (y1, ...) -> y1
      in
          E'

  GOAL: simplify the above to:

      E [ (x1,...,xn) := E' [y1 := x1,...,yn := xn] ]

  TODO: several tests (e.g. tests/pos/zipper000.hs) fail because
  the above changes the "type" the expression `E` and in "other branches"
  the new type may be different than the old, e.g.

     let (x::y::_) = e in
     x + y

     let t = case e of
               h1::t1 -> case t1 of
                            (h2::t2) ->  (h1, h2)
                            DEFAULT  ->  error @ (Int, Int)
               DEFAULT   -> error @ (Int, Int)
         x = case t of (h1, _) -> h1
         y = case t of (_, h2) -> h2
     in
         x + y

  is rewritten to:

              h1::t1     -> case t1 of
                            (h2::t2) ->  h1 + h2
                            DEFAULT  ->  error @ (Int, Int)
               DEFAULT   -> error @ (Int, Int)

     case e of
       h1 :: h2 :: _ -> h1 + h2
       DEFAULT       -> error @ (Int, Int)

  which, alas, is ill formed.

-}

--------------------------------------------------------------------------------

-- simplifyPatTuple :: RewriteRule
-- simplifyPatTuple e =
--  case simplifyPatTuple' e of
--    Just e' -> if CoreUtils.exprType e == CoreUtils.exprType e'
--                 then Just e'
--                 else Just (tracePpr ("YIKES: RWR " ++ showPpr e) e')
--    Nothing -> Nothing


_safeSimplifyPatTuple :: RewriteRule
_safeSimplifyPatTuple e
  | Just e' <- simplifyPatTuple e
  , CoreUtils.exprType e' == CoreUtils.exprType e
  = Just e'
  | otherwise
  = Nothing

--------------------------------------------------------------------------------
simplifyPatTuple :: RewriteRule
--------------------------------------------------------------------------------
simplifyPatTuple (Let (NonRec x e) rest)
  | Just (n, ts  ) <- varTuple x
  , 2 <= n
  , Just (yes, e') <- takeBinds n rest
  , let ys          = fst <$> yes
  , Just _         <- hasTuple ys e
  , matchTypes yes ts
  = replaceTuple ys e e'

simplifyPatTuple _
  = Nothing

varTuple :: Var -> Maybe (Int, [Type])
varTuple x
  | TyConApp c ts <- Var.varType x
  , isTupleTyCon c
  = Just (length ts, ts)
  | otherwise
  = Nothing

takeBinds  :: Nat -> CoreExpr -> Maybe ([(Var, CoreExpr)], CoreExpr)
takeBinds n e
  | n < 2     = Nothing
  | otherwise = mapFst reverse <$> go n e
    where
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
    xts           = Var.varType <$> xs
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
    t'                          = CoreUtils.exprType e'
    stepE e
     | Just xs <- isVarTup ys e = Just $ substTuple xs ys e'
     | otherwise                = go e
    stepA (DEFAULT, xs, err)    = Just (DEFAULT, xs, replaceIrrefutPat t' err)
    stepA (c, xs, e)            = (c, xs,)   <$> stepE e
    go (Let b e)                = Let b      <$> stepE e
    go (Case e x t cs)          = fixCase e x t <$> mapM stepA cs
    go _                        = Nothing


-- | The substitution (`substTuple`) can change the type of the overall
--   case-expression, so we must update the type of each `Case` with its
--   new, possibly updated type. See:
--   https://github.com/ucsd-progsys/liquidhaskell/pull/752#issuecomment-228946210

fixCase :: CoreExpr -> Var -> Type -> ListNE (Alt Var) -> CoreExpr
fixCase e x _t cs' = Case e x t' cs'
  where
    t'            = CoreUtils.exprType body
    (_,_,body)    = c
    c:_           = cs'

{-@  type ListNE a = {v:[a] | len v > 0} @-}
type ListNE a = [a]


replaceIrrefutPat :: Type -> CoreExpr -> CoreExpr
replaceIrrefutPat t (App (Lam z e) eVoid)
  | (Var x, _:args) <- collectArgs e
  , isIrrefutErrorVar x
  , let e' = MkCore.mkCoreApps (Var x) (Type t : args)
  = App (Lam z e') eVoid

replaceIrrefutPat _ e
  = e

isIrrefutErrorVar :: Var -> Bool
isIrrefutErrorVar x = MkCore.iRREFUT_PAT_ERROR_ID == x


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
