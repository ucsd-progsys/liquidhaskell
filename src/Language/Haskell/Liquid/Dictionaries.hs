module Language.Haskell.Liquid.Dictionaries where

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
makeDictionaryName t (RApp c _ _ _) = traceShow ("Symbol from " ++ show (t, c)) $  symbol ("$f" ++ (symbolString $ val t) ++ c')
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

dempty = DEnv M.empty

dmap f xts = M.map f xts

dinsert (DEnv denv) x xts = DEnv $ M.insert x xts denv

{-

dinsert (DEnv denv) x xts = DEnv $ M.insert x (M.fromList xts') denv
  where 
    xts'     = mapFst go <$> xts
    go       = symbol . drop 2 . show 

dinsert (DEnv denv) x xts = DEnv $ M.insert x (M.fromList xts') denv
  where 
    xts'     = mapFst go <$> xts
    go       = symbol . drop 2 . show 
-}

dlookup (DEnv denv) x     = M.lookup x denv


dhasinfo Nothing _    = Nothing
dhasinfo (Just xts) x = M.lookup x' xts
  where
     x' = (dropModuleNames $ symbol $ show x)