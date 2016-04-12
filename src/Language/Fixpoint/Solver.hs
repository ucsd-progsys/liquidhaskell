-- | This module implements the top-level API for interfacing with Fixpoint
--   In particular it exports the functions that solve constraints supplied
--   either as .fq files or as FInfo.
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Solver (
    -- * Invoke Solver on an FInfo
    solve, Solver

    -- * Invoke Solver on a .fq file
  , solveFQ

    -- * Function to determine outcome
  , resultExit

    -- * Parse Qualifiers from File
  , parseFInfo
) where

import           Control.Concurrent
import           Data.Binary
import           System.Exit                        (ExitCode (..))
import           System.Console.CmdArgs.Verbosity   (whenNormal)
import           Text.PrettyPrint.HughesPJ          (render)
import           Control.Monad                      (when)
import           Control.Exception                  (catch)
import           Language.Fixpoint.Solver.Validate  (sanitize)
import           Language.Fixpoint.Solver.UniqifyBinds (renameAll)
import           Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify)
import qualified Language.Fixpoint.Solver.Solve     as Sol
import           Language.Fixpoint.Types.Config           (queryFile, multicore, Config (..))
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files            hiding (Result)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Utils.Statistics (statistics)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Parse            (rr', mkQual)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Minimize (minQuery)
import           Control.DeepSeq


---------------------------------------------------------------------------
-- | Solve an .fq file ----------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg = do
    fi      <- readFInfo file
    r       <- solve cfg fi
    let stat = resStatus $!! r
    -- let str  = render $ resultDoc $!! (const () <$> stat)
    -- putStrLn "\n"
    whenNormal $ colorStrLn (colorResult stat) (statStr $!! stat)
    return $ eCode r
  where
    file    = inFile       cfg
    eCode   = resultExit . resStatus
    statStr = render . resultDoc . fmap fst

---------------------------------------------------------------------------
-- | Solve FInfo system of horn-clause constraints ------------------------
---------------------------------------------------------------------------
solve :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solve cfg q
  | parts cfg    = partition  cfg        $!! q
  | stats cfg    = statistics cfg        $!! q
  | minimize cfg = minQuery   cfg solve' $!! q
  | otherwise    = solve'     cfg        $!! q

solve' :: (NFData a, Fixpoint a) => Solver a
solve' cfg q = do
  when (save cfg) $ saveQuery   cfg q
  configSW  cfg     solveNative cfg q

configSW :: (NFData a, Fixpoint a) => Config -> Solver a -> Solver a
configSW cfg
  | multicore cfg = solveParWith
  | otherwise     = solveSeqWith

---------------------------------------------------------------------------
readFInfo :: FilePath -> IO (FInfo ())
---------------------------------------------------------------------------
readFInfo f        = fixFileName <$> act
  where
    fixFileName q  = q {fileName = f}
    act
      | isBinary f = readBinFq f
      | otherwise  = readFq f

readFq :: FilePath -> IO (FInfo ())
readFq file = do
  str   <- readFile file
  let q = {-# SCC "parsefq" #-} rr' file str :: FInfo ()
  return q

readBinFq :: FilePath -> IO (FInfo ())
readBinFq file = {-# SCC "parseBFq" #-} decodeFile file

---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveSeqWith :: (Fixpoint a) => Solver a -> Solver a
solveSeqWith s c fi0 = {- withProgressFI fi $ -} s c fi
  where
    fi               = slice fi0

---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveParWith :: (Fixpoint a) => Solver a -> Solver a
---------------------------------------------------------------------------
solveParWith s c fi0 = do
  -- putStrLn "Using Parallel Solver \n"
  let fi    = slice fi0
  mci      <- mcInfo c
  let fis   = partition' (Just mci) fi
  writeLoud $ "Number of partitions : " ++ show (length fis)
  writeLoud $ "number of cores      : " ++ show (cores c)
  writeLoud $ "minimum part size    : " ++ show (minPartSize c)
  writeLoud $ "maximum part size    : " ++ show (maxPartSize c)
  case fis of
    []        -> errorstar "partiton' returned empty list!"
    [onePart] -> s c onePart
    _         -> inParallelUsing (s c) fis

-------------------------------------------------------------------------------
-- | Solve a list of FInfos using the provided solver function in parallel
-------------------------------------------------------------------------------
inParallelUsing :: (a -> IO (Result b)) -> [a] -> IO (Result b)
-------------------------------------------------------------------------------
inParallelUsing f xs = do
   setNumCapabilities (length xs)
   rs <- asyncMapM f xs
   return $ mconcat rs

---------------------------------------------------------------------------
-- | Native Haskell Solver ------------------------------------------------
---------------------------------------------------------------------------
solveNative, solveNative' :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solveNative !cfg !fi0 = (solveNative' cfg fi0)
                          `catch`
                             (return . result)

result :: Error -> Result a
result e = Result (Crash [] msg) mempty
  where
    msg  = showpp e

solveNative' !cfg !fi0 = do
  -- writeLoud $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  -- rnf fi0 `seq` donePhase Loud "Read Constraints"
  -- let qs   = quals fi0
  -- whenLoud $ print qs
  let fi1  = fi0 { quals = remakeQual <$> quals fi0 }
  -- whenLoud $ putStrLn $ showFix (quals fi1)
  let si0   = {-# SCC "convertFormat" #-} convertFormat fi1
  -- writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si0)
  -- rnf si0 `seq` donePhase Loud "Format Conversion"
  let si1 = either die id $ {-# SCC "validate" #-} sanitize $!! si0
  -- writeLoud $ "fq file after validate: \n" ++ render (toFixpoint cfg si1)
  -- rnf si1 `seq` donePhase Loud "Validated Constraints"
  graphStatistics cfg si1
  let si2  = {-# SCC "wfcUniqify" #-} wfcUniqify $!! si1
  let si3  = {-# SCC "renameAll" #-} renameAll $!! si2
  rnf si3 `seq` donePhase Loud "Uniqify & Rename"
  res <- {-# SCC "Sol.solve" #-} Sol.solve cfg $!! si3
  -- rnf soln `seq` donePhase Loud "Solve2"
  --let stat = resStatus res
  saveSolution cfg res
  -- when (save cfg) $ saveSolution cfg
  -- writeLoud $ "\nSolution:\n"  ++ showpp (resSolution res)
  -- colorStrLn (colorResult stat) (show stat)
  return res

remakeQual :: Qualifier -> Qualifier
remakeQual q = {- traceShow msg $ -} mkQual (q_name q) (q_params q) (q_body q) (q_pos q)
--   where
--     msg      = "REMAKEQUAL: " ++ show q

---------------------------------------------------------------------------
-- | Extract ExitCode from Solver Result ----------------------------------
---------------------------------------------------------------------------
resultExit :: FixResult a -> ExitCode
---------------------------------------------------------------------------
resultExit Safe        = ExitSuccess
resultExit (Unsafe _)  = ExitFailure 1
resultExit _           = ExitFailure 2

--------------------------------------------------------------------------------
-- | Parse External Qualifiers -------------------------------------------------
--------------------------------------------------------------------------------
parseFInfo :: [FilePath] -> IO (FInfo a)
--------------------------------------------------------------------------------
parseFInfo fs = mconcat <$> mapM parseFI fs

parseFI :: FilePath -> IO (FInfo a) --[Qualifier]
parseFI f = do
  str   <- readFile f
  let fi = rr' f str :: FInfo ()
  return $ mempty { quals = quals  fi
                  , lits  = lits   fi }

saveSolution :: Config -> Result a -> IO ()
saveSolution cfg res = when (save cfg) $ do
  let f = queryFile Out cfg
  putStrLn $ "Saving Solution: " ++ f ++ "\n"
  ensurePath f
  writeFile f $ "\nSolution:\n"  ++ showpp (resSolution res)
