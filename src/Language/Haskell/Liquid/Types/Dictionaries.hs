{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}

module Language.Haskell.Liquid.Types.Dictionaries (
    makeDictionaries
  , makeDictionary

  , dfromList
  , dmapty
  , dmap
  , dinsert
  , dlookup
  , dhasinfo
  , mapRISig
  , fromRISig
  ) where

import           Data.Hashable
import           Prelude                                   hiding (error)
import           Var
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.PrettyPrint ()
import           Language.Haskell.Liquid.GHC.Misc          (dropModuleNamesCorrect)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType ()
import           Language.Fixpoint.Misc                (mapFst)

import qualified Data.HashMap.Strict                       as M

makeDictionaries :: [RInstance SpecType] -> DEnv F.Symbol SpecType
makeDictionaries = DEnv . M.fromList . map makeDictionary


makeDictionary :: RInstance SpecType -> (F.Symbol, M.HashMap F.Symbol (RISig SpecType))
makeDictionary (RI c ts xts) = (makeDictionaryName (btc_tc c) ts, M.fromList (mapFst val <$> xts))

makeDictionaryName :: Located F.Symbol -> [SpecType] -> F.Symbol
makeDictionaryName t ts
  = F.symbol ("$f" ++ F.symbolString (val t) ++ concatMap makeDicTypeName ts)


makeDicTypeName :: SpecType -> String
makeDicTypeName (RFun _ _ _ _)
  = "(->)"
makeDicTypeName (RApp c _ _ _)
  = F.symbolString $ dropModuleNamesCorrect $ F.symbol $ rtc_tc c
makeDicTypeName (RVar a _)
  = show a
makeDicTypeName t
  = panic Nothing ("makeDicTypeName: called with invalid type " ++ show t)


------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------ Dictionay Environment -------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------


dfromList :: [(Var, M.HashMap F.Symbol (RISig t))] -> DEnv Var t
dfromList = DEnv . M.fromList

dmapty :: (a -> b) -> DEnv v a -> DEnv v b
dmapty f (DEnv e) = DEnv (M.map (M.map (mapRISig f)) e)

mapRISig :: (a -> b) -> RISig a -> RISig b
mapRISig f (RIAssumed t) = RIAssumed (f t)
mapRISig f (RISig     t) = RISig     (f t)


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
     x' = (dropModuleNamesCorrect $ F.symbol x)
