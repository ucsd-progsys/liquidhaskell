-- | This module implements a "delta-debugging" based query minimizer.
--   Exported clients of that minimizer include one that attempts to
--   shrink UNSAT queries down to a minimal subset of constraints, and
--   one that shrinks SAT queries down to a minimal subset of qualifiers.

{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Minimize ( minQuery, minQuals ) where

import qualified Data.HashMap.Strict                as M
import           Control.Monad                      (filterM)
import           Language.Fixpoint.Types.Config     (Config (..))
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files      hiding (Result)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Types
import           Control.DeepSeq

---------------------------------------------------------------------------
-- polymorphic delta debugging implementation
---------------------------------------------------------------------------
deltaDebug :: Int -> Oracle a c -> Config -> Solver a -> FInfo a -> [c] -> [c] -> IO [c]
deltaDebug min testSet cfg solve finfo set r = do
  let (s1, s2) = splitAt (length set `div` 2) set
  if length set == min
    then return set
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

type Oracle a c = (Config -> Solver a -> FInfo a -> [c] -> IO Bool)


---------------------------------------------------------------------------
minQuery :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a
         -> IO (Result (Integer, a))
---------------------------------------------------------------------------
minQuery cfg solve fi = do
  let cfg'  = cfg { minimize = False }
  let fis   = partition' Nothing fi
  failFis  <- filterM (fmap (not . isSafe) . solve cfg') fis
  -- TODO: why concatMap? isn't the first (or smallest) set of failing cs good enough?
  failCs   <- concatMapM (getMinFailingCons cfg' solve) failFis
  -- TODO: the minFileName call here is useless because filenames are stored in
  -- both fi and cfg, and it's cfg's one that's used next. Could fix that here, but
  -- it may be better to refactor so that filename is stored only once
  let minFi = fi { cm = M.fromList failCs, fileName = minFileName fi }
  saveQuery cfg' minFi
  putStrLn $ "Minimized Constraints: " ++ show (fst <$> failCs)
  return mempty

minFileName :: FInfo a -> FilePath
minFileName = extFileName Min . fileName

type ConsList a = [(Integer, SubC a)]

testConstraints :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a -> ConsList a -> IO Bool
testConstraints cfg solve fi cons  = do
  let fi' = fi { cm = M.fromList cons }
  res <- solve cfg fi'
  return $ not $ isSafe res

-- run delta debugging on a failing partition to find minimal set of failing constraints
getMinFailingCons :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a -> IO (ConsList a)
getMinFailingCons cfg solve fi = do
  let cons = M.toList $ cm fi
  deltaDebug 1 testConstraints cfg solve fi cons []


---------------------------------------------------------------------------
minQuals :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a
         -> IO (Result (Integer, a))
---------------------------------------------------------------------------
minQuals cfg solve fi = do
  let cfg'  = cfg { minimizeQs = False }
  qs <- getMinPassingQuals cfg' solve fi
  let minFi = fi { quals = qs, fileName = minQualsName fi }
  saveQuery cfg' minFi
  putStrLn $ "Required Qualifiers: " ++ show (length qs)
          ++ "; Total Qualifiers: "  ++ show (length $ quals fi)
  return mempty

minQualsName :: FInfo a -> FilePath
minQualsName = extFileName Min . fileName

-- run delta debugging on a passing partition to find minimal set of necessary qualifiers
getMinPassingQuals :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a -> IO [Qualifier]
getMinPassingQuals cfg solve fi = do
  let qs = quals fi
  deltaDebug 0 testQuals cfg solve fi qs []

testQuals :: (NFData a, Fixpoint a) => Config -> Solver a -> FInfo a -> [Qualifier] -> IO Bool
testQuals cfg solve fi qs = do
  let fi' = fi { quals = qs }
  res <- solve cfg fi'
  return $ isSafe res

---------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------
isSafe :: Result a -> Bool
isSafe (Result Safe _) = True
isSafe _               = False

concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f
