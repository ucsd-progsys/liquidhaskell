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

    -- * Simplified Info 
  , simplifyFInfo
) where

import           Control.Concurrent
import           Data.Binary
import           System.Exit                        (ExitCode (..))
import           System.Console.CmdArgs.Verbosity   (whenNormal, whenLoud)
import           Text.PrettyPrint.HughesPJ          (render)
import           Control.Monad                      (when)
import           Control.Exception                  (catch)

import           Language.Fixpoint.Solver.Sanitize  (symbolEnv, sanitize)
import           Language.Fixpoint.Solver.UniqifyBinds (renameAll)
import           Language.Fixpoint.Defunctionalize (defunctionalize)
import           Language.Fixpoint.SortCheck            (Elaborate (..))
import           Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify)
import qualified Language.Fixpoint.Solver.Solve     as Sol
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files            hiding (Result)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Utils.Statistics (statistics)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Parse            (rr')
import           Language.Fixpoint.Types
import           Language.Fixpoint.Minimize (minQuery, minQuals, minKvars)
import           Language.Fixpoint.Solver.Instantiate (instantiate)
import           Control.DeepSeq

---------------------------------------------------------------------------
-- | Solve an .fq file ----------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg = solveFQ' cfg `catch` errorExit

errorExit :: Error -> IO ExitCode
errorExit e = do
  colorStrLn Sad ("Oops, unexpected error: " ++ showpp e)
  return (ExitFailure 2)

solveFQ' :: Config -> IO ExitCode
solveFQ' cfg = do
    (fi, opts) <- readFInfo file
    cfg'       <- withPragmas cfg opts
    let fi'     = ignoreQualifiers cfg' fi
    r          <- solve cfg' fi'
    let stat    = resStatus $!! r
    -- let str  = render $ resultDoc $!! (const () <$> stat)
    -- putStrLn "\n"
    whenNormal $ colorStrLn (colorResult stat) (statStr $!! stat)
    return $ eCode r
  where
    file    = srcFile      cfg
    eCode   = resultExit . resStatus
    statStr = render . resultDoc . fmap fst

ignoreQualifiers :: Config -> FInfo a -> FInfo a
ignoreQualifiers cfg fi
  | eliminate cfg == All = fi { quals = [] }
  | otherwise            = fi


--------------------------------------------------------------------------------
-- | Solve FInfo system of horn-clause constraints -----------------------------
--------------------------------------------------------------------------------
solve :: (NFData a, Fixpoint a, Show a, Loc a) => Solver a
--------------------------------------------------------------------------------
solve cfg q
  | parts cfg      = partition  cfg        $!! q
  | stats cfg      = statistics cfg        $!! q
  | minimize cfg   = minQuery   cfg solve' $!! q
  | minimizeQs cfg = minQuals cfg solve'   $!! q
  | minimizeKs cfg = minKvars cfg solve'   $!! q
  | otherwise      = solve'     cfg        $!! q

solve' :: (NFData a, Fixpoint a, Show a, Loc a) => Solver a
solve' cfg q = do
  when (save cfg) $ saveQuery   cfg q
  configSW  cfg     solveNative cfg q

configSW :: (NFData a, Fixpoint a, Show a, Loc a) => Config -> Solver a -> Solver a
configSW cfg
  | multicore cfg = solveParWith
  | otherwise     = solveSeqWith

--------------------------------------------------------------------------------
readFInfo :: FilePath -> IO (FInfo (), [String])
--------------------------------------------------------------------------------
readFInfo f
  | isBinary f = (,) <$> readBinFq f <*> return []
  | otherwise  = readFq f

readFq :: FilePath -> IO (FInfo (), [String])
readFq file = do
  str   <- readFile file
  let q  = {-# SCC "parsefq" #-} rr' file str :: FInfoWithOpts ()
  return (fioFI q, fioOpts q)

readBinFq :: FilePath -> IO (FInfo ())
readBinFq file = {-# SCC "parseBFq" #-} decodeFile file

--------------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
--------------------------------------------------------------------------------
solveSeqWith :: (Fixpoint a) => Solver a -> Solver a
solveSeqWith s c fi0 = {- withProgressFI fi $ -} s c fi
  where
    fi               = slice c fi0

--------------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
--------------------------------------------------------------------------------
solveParWith :: (Fixpoint a) => Solver a -> Solver a
--------------------------------------------------------------------------------
solveParWith s c fi0 = do
  -- putStrLn "Using Parallel Solver \n"
  let fi    = slice c fi0
  mci      <- mcInfo c
  let fis   = partition' (Just mci) fi
  writeLoud $ "Number of partitions : " ++ show (length fis)
  writeLoud $ "number of cores      : " ++ show (cores c)
  writeLoud $ "minimum part size    : " ++ show (minPartSize c)
  writeLoud $ "maximum part size    : " ++ show (maxPartSize c)
  case fis of
    []        -> errorstar "partiton' returned empty list!"
    [onePart] -> s c onePart
    _         -> inParallelUsing (f s c) $ zip [1..] fis
    where
      f s c (j, fi) = s (c {srcFile = queryFile (Part j) c}) fi

--------------------------------------------------------------------------------
-- | Solve a list of FInfos using the provided solver function in parallel
--------------------------------------------------------------------------------
inParallelUsing :: (a -> IO (Result b)) -> [a] -> IO (Result b)
--------------------------------------------------------------------------------
inParallelUsing f xs = do
   setNumCapabilities (length xs)
   rs <- asyncMapM f xs
   return $ mconcat rs

--------------------------------------------------------------------------------
-- | Native Haskell Solver -----------------------------------------------------
--------------------------------------------------------------------------------
solveNative, solveNative' :: (NFData a, Fixpoint a, Show a, Loc a) => Solver a
--------------------------------------------------------------------------------
solveNative !cfg !fi0 = (solveNative' cfg fi0)
                          `catch`
                             (return . result)

result :: Error -> Result a
result e = Result (Crash [] msg) mempty mempty
  where
    msg  = showpp e

loudDump :: (Fixpoint a) => Int -> Config -> SInfo a -> IO ()
loudDump i cfg si = writeLoud $ msg ++ render (toFixpoint cfg si)
  where
    msg           = "fq file after Uniqify & Rename " ++ show i ++ "\n"

simplifyFInfo :: (NFData a, Fixpoint a, Show a, Loc a)
               => Config -> FInfo a -> IO (SInfo a)
simplifyFInfo !cfg !fi0 = do 
  -- writeLoud $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  -- rnf fi0 `seq` donePhase Loud "Read Constraints"
  -- let qs   = quals fi0
  -- whenLoud $ print qs
  -- whenLoud $ putStrLn $ showFix (quals fi1)
  let fi1   = fi0 { quals = remakeQual <$> quals fi0 }
  let si0   = {-# SCC "convertFormat" #-} convertFormat fi1
  -- writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si0)
  -- rnf si0 `seq` donePhase Loud "Format Conversion"
  let si1   = either die id $ {-# SCC "sanitize" #-} sanitize $!! si0
  -- writeLoud $ "fq file after sanitize: \n" ++ render (toFixpoint cfg si1)
  -- rnf si1 `seq` donePhase Loud "Validated Constraints"
  graphStatistics cfg si1
  let si2  = {-# SCC "wfcUniqify" #-} wfcUniqify $!! si1
  let si3  = {-# SCC "renameAll"  #-} renameAll  $!! si2
  rnf si3 `seq` whenLoud $ donePhase Loud "Uniqify & Rename"
  loudDump 1 cfg si3
  let si4  = {-# SCC "defunction" #-} defunctionalize cfg $!! si3
  -- putStrLn $ "AXIOMS: " ++ showpp (asserts si4)
  loudDump 2 cfg si4
  let si5  = {-# SCC "elaborate"  #-} elaborate "solver" (symbolEnv cfg si4) si4
  loudDump 3 cfg si5
  instantiate cfg $!! si5

solveNative' !cfg !fi0 = do
  si6 <- simplifyFInfo cfg fi0 
  res <- {-# SCC "Sol.solve" #-} Sol.solve cfg $!! si6
  -- rnf soln `seq` donePhase Loud "Solve2"
  --let stat = resStatus res
  saveSolution cfg res
  -- when (save cfg) $ saveSolution cfg
  -- writeLoud $ "\nSolution:\n"  ++ showpp (resSolution res)
  -- colorStrLn (colorResult stat) (show stat)
  return res

--------------------------------------------------------------------------------
-- | Extract ExitCode from Solver Result ---------------------------------------
--------------------------------------------------------------------------------
resultExit :: FixResult a -> ExitCode
--------------------------------------------------------------------------------
resultExit Safe        = ExitSuccess
resultExit (Unsafe _)  = ExitFailure 1
resultExit _           = ExitFailure 2

--------------------------------------------------------------------------------
-- | Parse External Qualifiers -------------------------------------------------
--------------------------------------------------------------------------------
parseFInfo :: [FilePath] -> IO (FInfo a)
--------------------------------------------------------------------------------
parseFInfo fs = mconcat <$> mapM parseFI fs

parseFI :: FilePath -> IO (FInfo a)
parseFI f = do
  str   <- readFile f
  let fi = rr' f str :: FInfo ()
  return $ mempty { quals = quals  fi
                  , gLits = gLits  fi
                  , dLits = dLits  fi }

saveSolution :: Config -> Result a -> IO ()
saveSolution cfg res = when (save cfg) $ do
  let f = queryFile Out cfg
  putStrLn $ "Saving Solution: " ++ f ++ "\n"
  ensurePath f
  writeFile f $ "\nSolution:\n" ++ showpp (resSolution  res)
                ++ (if (gradual cfg) then ("\n\n" ++ showpp (gresSolution res)) else mempty)
