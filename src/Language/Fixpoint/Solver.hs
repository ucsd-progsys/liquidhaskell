-- | This module implements the top-level API for interfacing with Fixpoint
--   In particular it exports the functions that solve constraints supplied
--   either as .fq files or as FInfo.
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Solver (
    -- * Invoke Solver on an FInfo
    solve

    -- * Invoke Solver on a .fq file
  , solveFQ

    -- * Function to determine outcome
  , resultExit

    -- * Parse Qualifiers from File
  , parseFInfo
) where

import           Control.Concurrent
import           Data.Binary
import           Data.Maybe                         (fromMaybe)
import qualified Data.HashMap.Strict                as M
import qualified Data.HashSet                       as S
import           Data.List                          hiding (partition)
import           System.Exit                        (ExitCode (..))

import           System.Console.CmdArgs.Verbosity   hiding (Loud)
import           Text.PrettyPrint.HughesPJ          (render)
import           Text.Printf                        (printf)
import           Control.Monad                      (when, void)
import           Control.Exception                  (catch)

import           Language.Fixpoint.Solver.Graph     -- (slice)
import           Language.Fixpoint.Solver.Validate  (sanitize)
import           Language.Fixpoint.Solver.Eliminate (eliminateAll)
import           Language.Fixpoint.Solver.Deps      (deps, Deps (..))
import           Language.Fixpoint.Solver.UniqifyBinds (renameAll)
import           Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify)
import qualified Language.Fixpoint.Solver.Solve     as Sol
import           Language.Fixpoint.Solver.Solution  (Solution)
import           Language.Fixpoint.Types.Config           (multicore, Config (..), command, withTarget)
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files            hiding (Result)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Utils.Statistics (statistics)
import           Language.Fixpoint.Partition        (mcInfo, partition, partition')
import           Language.Fixpoint.Parse            (rr, rr', mkQual)
import           Language.Fixpoint.Types
import           Control.DeepSeq

---------------------------------------------------------------------------
-- | Top level Solvers ----------------------------------------------------
---------------------------------------------------------------------------

type Solver a = Config -> FInfo a -> IO (Result a)

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
    colorStrLn (colorResult stat) (statStr $!! stat)
    return $ eCode r
  where
    file    = inFile       cfg
    eCode   = resultExit . resStatus
    statStr = render . resultDoc . fmap (const ())

-- | Solve FInfo system of horn-clause constraints ------------------------
---------------------------------------------------------------------------
solve :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solve cfg fi
  | parts cfg = partition  cfg     $!! fi
  | stats cfg = statistics cfg     $!! fi
  | otherwise = do saveBin cfg     $!! fi
                   res <- sW s cfg $!! fi
                   return          $!! res {- FIXME make this $!! -}
  where
    s         = configSolver cfg
    sW        = configSW     cfg

saveBin :: (NFData a, Fixpoint a) => Config -> FInfo a -> IO ()
saveBin cfg fi = when (binary cfg) $ saveBinaryFile cfg fi
  -- putStrLn $ "Saving Binary File to: " ++ binaryFile cfg


configSolver   :: (NFData a, Fixpoint a) => Config -> Solver a
configSolver cfg
  | extSolver cfg = solveExt
  | otherwise     = solveNative

configSW :: (NFData a, Fixpoint a) => Config -> Solver a -> Solver a
configSW cfg
  | multicore cfg = solveParWith
  | otherwise     = solveSeqWith

---------------------------------------------------------------------------
readFInfo :: FilePath -> IO (FInfo ())
---------------------------------------------------------------------------
readFInfo f        = fixFileName <$> act
  where
    fixFileName fi = fi {fileName = f}
    act
      | isBinary f = readBinFq f
      | otherwise  = readFq f

readFq :: FilePath -> IO (FInfo ())
readFq file = do
  str   <- readFile file
  let fi = {-# SCC "parsefq" #-} rr' file str :: FInfo ()
  return fi

readBinFq :: FilePath -> IO (FInfo ())
readBinFq file = {-# SCC "parseBFq" #-} decodeFile file

---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveSeqWith :: (Fixpoint a) => Solver a -> Solver a
solveSeqWith s c fi0 = withProgressFI fi $ s c fi
  where
    fi               = slice fi0


---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveParWith :: (Fixpoint a) => Solver a -> Solver a
---------------------------------------------------------------------------
solveParWith s c fi0 = do
  -- putStrLn "Using Parallel Solver \n"
  let fi       = slice fi0
  withProgressFI fi $ do --progressInitFI fi
    mci <- mcInfo c
    let (_, fis) = partition' (Just mci) fi
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
solveNative !cfg !fi0 = (solveNative' cfg fi0) `catch` (return . result)

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
  whenLoud $ putStrLn $ showFix (quals fi1)
  let si0   = {-# SCC "convertFormat" #-} convertFormat fi1
  -- writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si0)
  -- rnf si0 `seq` donePhase Loud "Format Conversion"
  let si1 = either die id $ {-# SCC "validate" #-} sanitize $!! si0
  -- writeLoud $ "fq file after validate: \n" ++ render (toFixpoint cfg si1)
  -- rnf si1 `seq` donePhase Loud "Validated Constraints"
  when (elimStats cfg) $ printElimStats (deps si1)
  let si2  = {-# SCC "wfcUniqify" #-} wfcUniqify $!! si1
  let si3  = {-# SCC "renameAll" #-} renameAll $!! si2
  -- writeLoud $ "fq file after uniqify: \n" ++ render (toFixpoint cfg si2)
  -- rnf si2 `seq` donePhase Loud "Uniqify"
  (s0, si4) <- {-# SCC "elim" #-} elim cfg $!! si3
  res <- {-# SCC "Sol.solve" #-} Sol.solve cfg s0 $!! si4
  -- rnf soln `seq` donePhase Loud "Solve2"
  --let stat = resStatus res
  writeLoud $ "\nSolution:\n"  ++ showpp (resSolution res)
  -- colorStrLn (colorResult stat) (show stat)
  return res

printElimStats :: Deps -> IO ()
printElimStats d = putStrLn $ printf "KVars (Total/Post-Elim) = (%d, %d) \n" total postElims
  where
    total        = postElims + S.size (depNonCuts d)
    postElims    = S.size $ depCuts d

elim :: (Fixpoint a) => Config -> SInfo a -> IO (Solution, SInfo a)
elim cfg fi
  | eliminate cfg = do let (s0, fi') = eliminateAll fi
                       writeLoud $ "fq file after eliminate: \n" ++ render (toFixpoint cfg fi')
                       donePhase Loud "Eliminate"
                       return (s0, fi')
  | otherwise     = return (M.empty, fi)

remakeQual :: Qualifier -> Qualifier
remakeQual q = {- traceShow msg $ -} mkQual (q_name q) (q_params q) (q_body q) (q_pos q)
  where
    msg      = "REMAKEQUAL: " ++ show q

---------------------------------------------------------------------------
-- | External Ocaml Solver ------------------------------------------------
---------------------------------------------------------------------------
solveExt :: (Fixpoint a) => Solver a
solveExt cfg fi =   {-# SCC "Solve"  #-} execFq cfg fn fi
                >>= {-# SCC "exitFq" #-} exitFq fn (cm fi)
  where
    fn          = fileName fi -- srcFile cfg

execFq :: (Fixpoint a) => Config -> FilePath -> FInfo a -> IO ExitCode
execFq cfg fn fi
  = do ensurePath fq
       writeFile fq $ render $ {-# SCC "FixPointify" #-} toFixpoint cfg fi
       solveFile $ cfg `withTarget` fq
    where
       fq   = extFileName Fq fn

solveFile :: Config -> IO ExitCode
solveFile cfg
  = do fp <- getFixpointPath
       z3 <- getZ3LibPath
       v  <- (\b -> if b then "-v 1" else "") <$> isLoud
       {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ fixCommand fp z3 v
    where
      fixCommand fp z3 verbosity
        = printf "LD_LIBRARY_PATH=%s %s %s %s -notruekvars -refinesort -nosimple -strictsortcheck -sortedquals %s %s"
          z3 fp verbosity rf newcheckf (command cfg)
        where
          rf  = if real cfg then realFlags else ""
          newcheckf = if newcheck cfg then "-newcheck" else ""

realFlags :: String
realFlags =  "-no-uif-multiply "
          ++ "-no-uif-divide "


exitFq :: (Fixpoint a) => FilePath -> M.HashMap Integer (SubC a) -> ExitCode -> IO (Result a)
exitFq _ _ (ExitFailure n) | n /= 1
  = return $ Result (Crash [] "Unknown Error") M.empty
exitFq fn z _
  = do str <- {-# SCC "readOut" #-} readFile (extFileName Out fn)
       let (x, y) = parseFixpointOutput str
       let x'     = fmap (mlookup z) x
       return     $ Result (sinfo <$> x') y

parseFixpointOutput :: String -> (FixResult Integer, FixSolution)
parseFixpointOutput str = {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)

sanitizeFixpointOutput :: String -> String
sanitizeFixpointOutput
  = unlines
  . filter (not . ("//"     `isPrefixOf`))
  . chopAfter ("//QUALIFIERS" `isPrefixOf`)
  . lines

chopAfter ::  (a -> Bool) -> [a] -> [a]
chopAfter f xs
  = case findIndex f xs of
      Just n  -> take n xs
      Nothing -> xs


---------------------------------------------------------------------------
-- | Extract ExitCode from Solver Result ----------------------------------
---------------------------------------------------------------------------
resultExit :: FixResult a -> ExitCode
---------------------------------------------------------------------------
resultExit Safe        = ExitSuccess
resultExit (Unsafe _)  = ExitFailure 1
resultExit _           = ExitFailure 2


---------------------------------------------------------------------------
-- | Parse External Qualifiers --------------------------------------------
---------------------------------------------------------------------------
parseFInfo :: [FilePath] -> IO (FInfo a) -- [Qualifier]
---------------------------------------------------------------------------
parseFInfo fs = mconcat <$> mapM parseFI fs

parseFI :: FilePath -> IO (FInfo a) --[Qualifier]
parseFI f = do
  str   <- readFile f
  let fi = rr' f str :: FInfo ()
  return $ mempty { quals = quals  fi
                  , lits  = lits   fi }

---------------------------------------------------------------------------
-- | Save Query to Binary File
---------------------------------------------------------------------------
saveBinary :: Config -> IO ExitCode
---------------------------------------------------------------------------
saveBinary cfg
  | isBinary f = return ExitSuccess
  | otherwise  = exit (ExitFailure 2) $ readFInfo f >>=
                                        saveBinaryFile cfg >>
                                        return ExitSuccess
  where
    f          = inFile cfg

saveBinaryFile :: Config -> FInfo a -> IO ()
saveBinaryFile cfg fi = do
  let fi'  = void fi
  let file = binaryFile cfg
  -- putStrLn $ "Saving Binary File: " ++ file ++ "\n"
  ensurePath file
  encodeFile file fi'

binaryFile :: Config -> FilePath
binaryFile cfg = extFileName BinFq f
  where
    f          = fromMaybe "out" $ find (not . null) [srcFile cfg, inFile cfg]

isBinary :: FilePath -> Bool
isBinary = isExtFile BinFq


---------------------------------------------------------------------------
-- | Initialize Progress Bar
---------------------------------------------------------------------------
withProgressFI :: FInfo a -> IO b -> IO b
---------------------------------------------------------------------------
withProgressFI = withProgress . fromIntegral . gSccs . cGraph
