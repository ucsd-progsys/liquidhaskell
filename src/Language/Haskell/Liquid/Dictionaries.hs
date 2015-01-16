module Language.Haskell.Liquid.Dictionaries (
    makeDictionaries
  , makeDictionary

  , dfromList
  , dmapty
  , dmap
  , dinsert
  , dlookup
  , dhasinfo
  ) where

import Control.Applicative      ((<$>))

import Var


import Language.Fixpoint.Names      (dropModuleNames)
import Language.Fixpoint.Types
import Language.Fixpoint.Misc 

import Language.Haskell.Liquid.GhcMisc ()
import Language.Haskell.Liquid.Types

import qualified Data.HashMap.Strict as M
import Language.Haskell.Liquid.PrettyPrint ()

makeDictionaries :: [RInstance SpecType] -> DEnv Symbol SpecType
makeDictionaries = DEnv . M.fromList . map makeDictionary


makeDictionary :: RInstance SpecType -> (Symbol, M.HashMap Symbol SpecType)
makeDictionary (RI c t xts) = (makeDictionaryName c t, M.fromList (mapFst val <$> xts))

makeDictionaryName :: Located Symbol -> SpecType -> Symbol
makeDictionaryName t (RApp c _ _ _) = symbol ("$f" ++ (symbolString $ val t) ++ c')
  where 
  	c' = symbolString (dropModuleNames $ symbol $ rtc_tc c)

makeDictionaryName _ _              = errorstar "makeDictionaryName: called with invalid type"

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------ Dictionay Environment -------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------


dfromList :: [(Var, M.HashMap Symbol t)] -> DEnv Var t
dfromList = DEnv . M.fromList

dmapty :: (a -> b) -> DEnv v a -> DEnv v b
dmapty f (DEnv e) = DEnv (M.map (M.map f) e)

dmap f xts = M.map f xts

dinsert (DEnv denv) x xts = DEnv $ M.insert x xts denv

dlookup (DEnv denv) x     = M.lookup x denv


dhasinfo Nothing _    = Nothing
dhasinfo (Just xts) x = M.lookup x' xts
  where
     x' = (dropModuleNames $ symbol $ show x)

