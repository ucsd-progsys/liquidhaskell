-- | This module implements a "delta-debugging" based query minimizer.
--   Exported clients of that minimizer include one that attempts to
--   shrink UNSAT queries down to a minimal subset of constraints,
--   one that shrinks SAT queries down to a minimal subset of qualifiers,
--   and one that shrinks SAT queries down to a minimal subset of KVars
--   (replacing all others by True).

{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Minimize ( minQuery, minQuals, minKvars ) where

import qualified Data.HashMap.Strict                as M
import           Control.Monad                      (filterM)
import           Language.Fixpoint.Types.Visitor    (mapKVars)
import           Language.Fixpoint.Types.Config     (Config (..), queryFile)
import           Language.Fixpoint.Misc             (safeHead)
import           Language.Fixpoint.Utils.Files      hiding (Result)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Types
import           Control.DeepSeq

---------------------------------------------------------------------------
-- polymorphic delta debugging implementation
---------------------------------------------------------------------------
deltaDebug :: Bool -> Oracle a c -> Config -> Solver a -> FInfo a -> [c] -> [c] -> IO [c]
deltaDebug min testSet cfg solve finfo set r = do
  let (s1, s2) = splitAt (length set `div` 2) set
  if length set == 1
    then deltaDebug1 min testSet cfg solve finfo set r
    else do
      test1 <- testSet cfg solve finfo (s1 ++ r)
      if test1
        then deltaDebug min testSet cfg solve finfo s1 r
        else do
          test2 <- testSet cfg solve finfo (s2 ++ r)
          if test2
            then deltaDebug min testSet cfg solve finfo s2 r
            else do
              d1 <- deltaDebug min testSet cfg solve finfo s1 (s2 ++ r)
              d2 <- deltaDebug min testSet cfg solve finfo s2 (d1 ++ r)
              return (d1 ++ d2)

deltaDebug1 :: Bool -> (a -> b -> c -> d -> IO Bool)
            -> a -> b -> c -> [e] -> d
            -> IO [e]
deltaDebug1 True  _       _   _     _     set _ = return set
deltaDebug1 False testSet cfg solve finfo set r = do
  test <- testSet cfg solve finfo r
  if test then return [] else return set

type Oracle a c = (Config -> Solver a -> FInfo a -> [c] -> IO Bool)

commonDebug :: (NFData a, Fixpoint a) => (FInfo a -> [c])
                                      -> (FInfo a -> [c] -> FInfo a)
                                      -> (Result (Integer, a) -> Bool)
                                      -> Bool
                                      -> Config
                                      -> Solver a
                                      -> FInfo a
                                      -> Ext
                                      -> (FInfo a -> [c] -> String)
                                      -> IO (Result (Integer, a))
commonDebug init updateFi checkRes min cfg solve fi ext formatter = do
  let cs0 = init fi
  let oracle = mkOracle updateFi checkRes
  cs <- deltaDebug min oracle cfg solve fi cs0 []
  let minFi = updateFi fi cs
  saveQuery (addExt ext cfg) minFi
  putStrLn $ formatter fi cs
  return mempty

---------------------------------------------------------------------------
minQuery :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a
         -> IO (Result (Integer, a))
---------------------------------------------------------------------------
minQuery cfg solve fi = do
  let cfg'  = cfg { minimize = False }
  let fis   = partition' Nothing fi
  failFis  <- filterM (fmap (not . isSafe) . solve cfg') fis
  let failFi = safeHead "--minimize can only be called on UNSAT fq" failFis
  let format _ cs = "Minimized Constraints: " ++ show (fst <$> cs)
  let update fi cs = fi { cm = M.fromList cs }
  commonDebug (M.toList . cm) update (not . isSafe) True cfg' solve failFi Min format

---------------------------------------------------------------------------
minQuals :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a
         -> IO (Result (Integer, a))
---------------------------------------------------------------------------
minQuals cfg solve fi = do
  let cfg'  = cfg { minimizeQs = False }
  let format fi qs = "Required Qualifiers: " ++ show (length qs)
                  ++ "; Total Qualifiers: "  ++ show (length $ quals fi)
  let update fi qs = fi { quals = qs }
  commonDebug quals update isSafe False cfg' solve fi MinQuals format

---------------------------------------------------------------------------
minKvars :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a
         -> IO (Result (Integer, a))
---------------------------------------------------------------------------
minKvars cfg solve fi = do
  let cfg'  = cfg { minimizeKs = False }
  let format fi ks = "Required KVars: " ++ show (length ks)
                  ++ "; Total KVars: "  ++ show (length $ ws fi)
  commonDebug (M.keys . ws) removeOtherKs isSafe False cfg' solve fi MinKVars format

removeOtherKs :: FInfo a -> [KVar] -> FInfo a
removeOtherKs fi0 ks = fi1 { ws = ws', cm = cm' }
  where
    fi1 = mapKVars go fi0
    go k | k `elem` ks = Nothing
         | otherwise   = Just PTrue
    ws' = M.filterWithKey (\k _ -> k `elem` ks) $ ws fi1
    cm' = M.filter (isNonTrivial . srhs) $ cm fi1

---------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------
addExt :: Ext -> Config -> Config
addExt ext cfg = cfg { srcFile = queryFile ext cfg }

mkOracle :: (NFData a, Fixpoint a) => (FInfo a -> [c] -> FInfo a)
                                   -> (Result (Integer, a) -> Bool)
                                   -> Oracle a c
mkOracle updateFi checkRes cfg solve fi qs = do
  let fi' = updateFi fi qs
  res <- solve cfg fi'
  return $ checkRes res
