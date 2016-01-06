{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

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
import           Data.Maybe                          (fromMaybe, maybeToList)
import           Language.Fixpoint.Misc              (traceShow)
import           Language.Fixpoint.Types             hiding (Error, SrcSpan, shiftVV)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.Simplify
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Misc        (single)

type Ctx = M.HashMap Symbol SpecType

------------------------------------------------------------------------
tidyError :: FixSolution -> Error -> Error
------------------------------------------------------------------------
tidyError sol
  = fmap (tidySpecType Full)
  . tidyErrContext sol
  . applySolution sol

tidyErrContext :: FixSolution -> Error -> Error
tidyErrContext _ e@(ErrSubType {})
  = e { ctx = c', tact = subst θ tA, texp = subst θ tE }
    where
      (θ, c') = tidyCtx xs $ ctx e
      xs      = syms tA ++ syms tE
      tA      = tact e
      tE      = texp e

tidyErrContext _ e@(ErrAssType {})
  = e { ctx = c', cond = subst θ p }
    where
      (θ, c') = tidyCtx xs $ ctx e
      xs      = syms p
      p       = cond e

tidyErrContext _ e
  = e

--------------------------------------------------------------------------------
tidyCtx       :: [Symbol] -> Ctx -> (Subst, Ctx)
--------------------------------------------------------------------------------
tidyCtx xs m  = (θ, M.fromList yts')
  where
    yts'      = {- traceShow ("tidyCtx: xs = " ++ show xs ++ "\nm = " ++ show m) -} yts
    yts       = [tBind x t | (x, t) <- xts]
    (θ, xts)  = tidyTemps $ second stripReft <$> tidyREnv xs m
    tBind x t = (x', shiftVV t x') where x' = tidySymbol x


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

tidyREnv      :: [Symbol] -> Ctx -> [(Symbol, SpecType)]
tidyREnv xs m = [(x, t) | x <- xs', t <- maybeToList (M.lookup x m), ok t]
  where
    xs'       = expandFix deps xs
    deps y    = fromMaybe [] $ fmap (syms . rTypeReft) $ M.lookup y m
    ok        = not . isFunTy

expandFix :: (Eq a, Hashable a) => (a -> [a]) -> [a] -> [a]
expandFix f               = S.toList . go S.empty
  where
    go seen []            = seen
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise         = go (S.insert x seen) (f x ++ xs)

tidyTemps     :: (Subable t) => [(Symbol, t)] -> (Subst, [(Symbol, t)])
tidyTemps xts = (θ, [(txB x, txTy t) | (x, t) <- xts])
  where
    txB  x    = M.lookupDefault x x m
    txTy      = subst θ
    m         = M.fromList yzs
    θ         = mkSubst [(y, EVar z) | (y, z) <- yzs]
    yzs       = zip ys niceTemps
    ys        = [ x | (x,_) <- xts, isTmpSymbol x]

niceTemps     :: [Symbol]
niceTemps     = mkSymbol <$> xs ++ ys
  where
    mkSymbol  = symbol . ('?' :)
    xs        = single   <$> ['a' .. 'z']
    ys        = ("a" ++) <$> [show n | n <- [0 ..]]
