{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
module Language.Haskell.Liquid.Types.Dictionaries (
    dfromList
  , dmapty
  , dmap
  , dinsert
  , dlookup
  , dhasinfo
  , fromRISig
  ) where

import           Data.Hashable

import           Prelude                                   hiding (error)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.PrettyPrint ()
import qualified Language.Haskell.Liquid.GHC.Misc       as GM
import qualified Liquid.GHC.API        as Ghc
-- import           Language.Haskell.Liquid.Types.Visitors (freeVars)
import           Language.Haskell.Liquid.Types.RefType ()
import           Language.Haskell.Liquid.Types.Types
import qualified Data.HashMap.Strict                       as M


--------------------------------------------------------------------------------
-- | Dictionary Environment ----------------------------------------------------
--------------------------------------------------------------------------------

dfromList :: [(Ghc.Var, M.HashMap F.Symbol (RISig t))] -> DEnv Ghc.Var t
dfromList = DEnv . M.fromList

dmapty :: (a -> b) -> DEnv v a -> DEnv v b
dmapty f (DEnv e) = DEnv (M.map (M.map (fmap f)) e)

-- REBARE: mapRISig :: (a -> b) -> RISig a -> RISig b
-- REBARE: mapRISig f (RIAssumed t) = RIAssumed (f t)
-- REBARE: mapRISig f (RISig     t) = RISig     (f t)

fromRISig :: RISig a -> a
fromRISig (RIAssumed t) = t
fromRISig (RISig     t) = t

dmap :: (v1 -> v2) -> M.HashMap k v1 -> M.HashMap k v2
dmap f xts = M.map f xts

dinsert :: (Eq x, Hashable x)
        => DEnv x ty -> x -> M.HashMap F.Symbol (RISig ty) -> DEnv x ty
dinsert (DEnv denv) x xts = DEnv $ M.insert x xts denv

dlookup :: (Eq k, Hashable k)
        => DEnv k t -> k -> Maybe (M.HashMap F.Symbol (RISig t))
dlookup (DEnv denv) x     = M.lookup x denv


dhasinfo :: (F.Symbolic a1, Show a) => Maybe (M.HashMap F.Symbol a) -> a1 -> Maybe a
dhasinfo Nothing _    = Nothing
dhasinfo (Just xts) x = M.lookup x' xts
  where
     x'               = GM.dropModuleNamesCorrect (F.symbol x)
