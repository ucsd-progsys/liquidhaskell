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
  , fromRISig
  ) where

import           Data.Hashable
-- import           Data.Maybe (catMaybes)

import           Prelude                                   hiding (error)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.PrettyPrint ()
import qualified Liquid.GHC.Misc       as GM
import qualified Liquid.GHC.API        as Ghc
import           Language.Haskell.Liquid.Types.Types
-- import           Language.Haskell.Liquid.Types.Visitors (freeVars)
import           Language.Haskell.Liquid.Types.RefType ()
import           Language.Fixpoint.Misc                (mapFst)
import qualified Data.HashMap.Strict                       as M





makeDictionaries :: [RInstance LocSpecType] -> DEnv F.Symbol LocSpecType
makeDictionaries = DEnv . M.fromList . map makeDictionary


makeDictionary :: RInstance LocSpecType -> (F.Symbol, M.HashMap F.Symbol (RISig LocSpecType))
makeDictionary (RI c ts xts) = (makeDictionaryName (btc_tc c) ts, M.fromList (mapFst val <$> xts))

makeDictionaryName :: LocSymbol -> [LocSpecType] -> F.Symbol
makeDictionaryName t ts
  = F.notracepp _msg $ F.symbol ("$f" ++ F.symbolString (val t) ++ concatMap mkName ts)
  where
    mkName = makeDicTypeName sp . dropUniv . val
    sp     = GM.fSrcSpan t
    _msg   = "MAKE-DICTIONARY " ++ F.showpp (val t, ts)

-- | @makeDicTypeName@ DOES NOT use show/symbol in the @RVar@ case 
--   as those functions add the unique-suffix which then breaks the 
--   class resolution.

makeDicTypeName :: Ghc.SrcSpan -> SpecType -> String
makeDicTypeName _ RFun{}           = "(->)"
makeDicTypeName _ (RApp c _ _ _)   = F.symbolString . GM.dropModuleNamesCorrect . F.symbol . rtc_tc $ c
makeDicTypeName _ (RVar (RTV a) _) = show (Ghc.getName a)
makeDicTypeName sp t               = panic (Just sp) ("makeDicTypeName: called with invalid type " ++ show t)

dropUniv :: SpecType -> SpecType
dropUniv t = t' where (_,_,t') = bkUniv t

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
