{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

-- | This module contains the functions related to @Error@ type,
-- in particular, to @tidyError@ using a solution, and @pprint@ errors.

-- TODO: move this into Tidy.

module Language.Haskell.Liquid.UX.Errors
  ( -- * Cleanup an Error
    tidyError
 ) where

import           Control.Arrow                       (second)
import qualified Data.HashMap.Strict                 as M
import qualified Data.HashSet                        as S
import           Data.Hashable
import           Data.Maybe                          (maybeToList)
import qualified Language.Fixpoint.Types             as F -- hiding (Error, SrcSpan, shiftVV)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.Simplify
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Misc as Misc 
import qualified Language.Fixpoint.Misc       as Misc 

-- import Debug.Trace

type Ctx  = M.HashMap F.Symbol SpecType
type CtxM = M.HashMap F.Symbol (WithModel SpecType)

------------------------------------------------------------------------
tidyError :: F.FixSolution -> Error -> Error
------------------------------------------------------------------------
tidyError sol
  = fmap (tidySpecType F.Full)
  . tidyErrContext sol

tidyErrContext :: F.FixSolution -> Error -> Error
tidyErrContext _ e@(ErrSubType {})
  = e { ctx = c', tact = F.subst θ tA, texp = F.subst θ tE }
    where
      (θ, c') = tidyCtx xs $ ctx e
      xs      = F.syms tA ++ F.syms tE
      tA      = tact e
      tE      = texp e

tidyErrContext _ e@(ErrSubTypeModel {})
  = e { ctxM = c', tactM = fmap (F.subst θ) tA, texp = fmap (F.subst θ) tE }
    where
      (θ, c') = tidyCtxM xs $ ctxM e
      xs      = F.syms tA ++ F.syms tE
      tA      = tactM e
      tE      = texp e

tidyErrContext _ e@(ErrAssType {})
  = e { ctx = c', cond = F.subst θ p }
    where
      m       = ctx e
      (θ, c') = tidyCtx xs m
      xs      = F.syms p
      p       = cond e

tidyErrContext _ e
  = e

--------------------------------------------------------------------------------
tidyCtx       :: [F.Symbol] -> Ctx -> (F.Subst, Ctx)
--------------------------------------------------------------------------------
tidyCtx xs m   = (θ1 `mappend` θ2, M.fromList yts)
  where
    yts        = [tBind x (tidySpecType F.Full t) | (x, t) <- xt2s]
    (θ2, xt2s) = tidyTemps xt1s -- [ (x, stripReft t) | (x, t) <- xt1s ] 
    (θ1, xt1s) = tidyREnv xs m 
    tBind x t  = (x', shiftVV t x') where x' = F.tidySymbol x

tidyCtxM       :: [F.Symbol] -> CtxM -> (F.Subst, CtxM)
tidyCtxM xs m  = (θ, M.fromList yts)
  where
    yts       = [tBind x t | (x, t) <- xts]
    (θ, xts)  = tidyTemps $ second (fmap stripReft) <$> tidyREnvM xs m
    tBind x t = (x', fmap (\t -> shiftVV t x') t) where x' = F.tidySymbol x


stripReft     :: SpecType -> SpecType
stripReft t   = maybe t' (strengthen t') ro
  where
    (t', ro)  = stripRType t

stripRType    :: SpecType -> (SpecType, Maybe RReft)
stripRType st = (t', ro)
  where
    t'        = fmap (const (uTop mempty)) t
    ro        = stripRTypeBase  t
    t         = simplifyBounds st

tidyREnv :: [F.Symbol] -> Ctx -> (F.Subst, [(F.Symbol, SpecType)])
tidyREnv xs m   = (θ, second (F.subst θ) <$> zts) -- [(z, F.subst θ t) | (z, t) <- zts]) 
  where 
    θ           = mconcat [ F.mkSubst [(y, e)] | (y, e) <- yes ]
    (yes, zts)  = Misc.mapEither isInline xts 
    xts         = sliceREnv xs m

isInline :: (a, SpecType) -> Either (a, F.Expr) (a, SpecType) 
isInline (x, t) = either (Left . (x,)) (Right . (x,)) (isInline' t) 

isInline' :: SpecType -> Either F.Expr SpecType 
isInline' t = case ro of 
                Nothing -> Right t' 
                Just rr -> case F.isSingletonReft (ur_reft rr) of 
                             Just e  -> Left e
                             Nothing -> Right (strengthen t' rr) 
              where 
                  (t', ro) = stripRType t 



sliceREnv :: [F.Symbol] -> Ctx -> [(F.Symbol, SpecType)]
sliceREnv xs m = [(x, t) | x <- xs', t <- maybeToList (M.lookup x m), ok t]
  where
    xs'       = expandFix deps xs
    deps y    = maybe [] (F.syms . rTypeReft) (M.lookup y m)
    ok        = not . isFunTy

tidyREnvM      :: [F.Symbol] -> CtxM -> [(F.Symbol, WithModel SpecType)]
tidyREnvM xs m = [(x, t) | x <- xs', t <- maybeToList (M.lookup x m), ok t]
  where
    xs'       = expandFix deps xs
    deps y    = maybe [] (F.syms . rTypeReft . dropModel) (M.lookup y m)
    ok        = not . isFunTy . dropModel

expandFix :: (Eq a, Hashable a) => (a -> [a]) -> [a] -> [a]
expandFix f               = S.toList . go S.empty
  where
    go seen []            = seen
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise         = go (S.insert x seen) (f x ++ xs)

tidyTemps     :: (F.Subable t) => [(F.Symbol, t)] -> (F.Subst, [(F.Symbol, t)])
tidyTemps xts = (θ, [(txB x, txTy t) | (x, t) <- xts])
  where
    txB  x    = M.lookupDefault x x m
    txTy      = F.subst θ
    m         = M.fromList yzs
    θ         = F.mkSubst [(y, F.EVar z) | (y, z) <- yzs]
    yzs       = zip ys niceTemps
    ys        = [ x | (x,_) <- xts, isTmpSymbol x]

niceTemps     :: [F.Symbol]
niceTemps     = mkSymbol <$> xs ++ ys
  where
    mkSymbol  = F.symbol . ('?' :)
    xs        = Misc.single <$> ['a' .. 'z']
    ys        = ("a" ++) <$> [show n | n <- [0 ..]]
