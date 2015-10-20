-- | This module implements the top-level API for interfacing with Fixpoint
--   In particular it exports the functions that solve constraints supplied
--   either as .fq files or as FInfo.
{-# LANGUAGE BangPatterns #-}

module Language.Fixpoint.Interface (
    -- * Invoke Solver on an FInfo
    solve

    -- * Invoke Solver on a .fq file
  , solveFQ

    -- * Function to determine outcome
  , resultExit

    -- * Parse Qualifiers from File
  , parseFInfo
) where

<<<<<<< HEAD
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor ((<$>))
import           Data.Monoid (mconcat, mempty)
#endif

=======
>>>>>>> master
import           Data.Binary
import           Data.Maybe                         (fromMaybe)
import qualified Data.HashMap.Strict                as M
import           Data.List                          hiding (partition)
import           System.Exit                        (ExitCode (..))

import           System.Console.CmdArgs.Verbosity   hiding (Loud)
import           Text.PrettyPrint.HughesPJ          (render)
import           Text.Printf                        (printf)
import           Control.Monad                      (when, void)

<<<<<<< HEAD
import           Language.Fixpoint.Solver.Graph     -- (slice)
import           Language.Fixpoint.Solver.Validate  (validate)
=======
import           Language.Fixpoint.Solver.Validate  (sanitize)
>>>>>>> master
import           Language.Fixpoint.Solver.Eliminate (eliminateAll)
import           Language.Fixpoint.Solver.Deps      (deps, Deps (..))
import           Language.Fixpoint.Solver.Uniqify   (renameAll)
import qualified Language.Fixpoint.Solver.Solve     as S
import           Language.Fixpoint.Solver.Solution  (Solution)
import           Language.Fixpoint.Config           (multicore, Config (..), command, withTarget)
import           Language.Fixpoint.Files            hiding (Result)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Statistics       (statistics)
import           Language.Fixpoint.Partition        (partition, partition')
import           Language.Fixpoint.Parse            (rr, rr', mkQual)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Errors           (exit)
import           Language.Fixpoint.PrettyPrint      (showpp)
import           Language.Fixpoint.Parallel         (inParallelUsing)
import           Control.DeepSeq

---------------------------------------------------------------------------
-- | Top level Solvers ----------------------------------------------------
---------------------------------------------------------------------------

type Solver a = Config -> FInfo a -> IO (Result a)

-- | Solve an .fq file ----------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg = do fi      <- readFInfo file
                 r       <- solve cfg fi
                 let stat = resStatus r
                 putStrLn "\n"
                 colorStrLn (colorResult stat) (show stat)
                 return $ eCode r
  where
    file    = inFile       cfg
    eCode   = resultExit . resStatus

-- | Solve FInfo system of horn-clause constraints ------------------------
---------------------------------------------------------------------------
solve :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solve cfg fi
  | parts cfg = partition  cfg $!! fi
  | stats cfg = statistics cfg $!! fi
  | otherwise = do saveBin cfg $!! fi
                   sW s    cfg $!! fi
  where
    s         = configSolver cfg
    sW        = configSW     cfg

saveBin :: (NFData a, Fixpoint a) => Config -> FInfo a -> IO ()
saveBin cfg fi = when (binary cfg) $ do
  putStrLn $ "Saving Binary File to: " ++ binaryFile cfg
  saveBinaryFile cfg fi


configSolver   :: (NFData a, Fixpoint a) => Config -> Solver a
configSolver cfg
  | native cfg = solveNative
  | otherwise  = solveExt

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
solveSeqWith s c fi0 = do
  putStrLn "Using Sequential Solver \n"
  let fi = slice fi0
  progressInitFI fi
  s c fi


---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveParWith :: (Fixpoint a) => Solver a -> Solver a
---------------------------------------------------------------------------
solveParWith s c fi0 = do
  putStrLn "Using Parallel Solver \n"
  let fi       = slice fi0
  progressInitFI fi
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

-- DEBUG debugDiff :: FInfo a -> FInfo b -> IO ()
-- DEBUG debugDiff fi fi' = putStrLn msg
  -- DEBUG where
    -- DEBUG {- msg          = printf "\nDEBUG: diff = %s, cs = %s, ws = %s, bs = %s, \n lits = %s \n, \n lits' = %s"
                     -- DEBUG (show $ ufi      == ufi')
                     -- DEBUG (show $ cm ufi   == cm   ufi')
                     -- DEBUG (show $ ws ufi   == ws   ufi')
                     -- DEBUG (show $ bs ufi   == bs   ufi')
                     -- DEBUG -- (show $ lits ufi == lits ufi')
                     -- DEBUG (show $ lits ufi)
                     -- DEBUG (show $ lits ufi') -}
-- DEBUG
    -- DEBUG msg          = printf "\nquals = %s\n\n\nquals' = %s"
                     -- DEBUG (show $ sort $ quals fi)
                     -- DEBUG (show $ sort $ quals fi')
-- DEBUG
    -- DEBUG (ufi, ufi')  = (fu <$> fi    ,  fu <$> fi')
    -- DEBUG fu           = const ()
    -- DEBUG (ncs, ncs')  = (cLength  fi  , cLength fi')
    -- DEBUG (nws, nws')  = (wLength  fi  , wLength fi')
    -- DEBUG (nbs, nbs')  = (beLength fi  , beLength fi')
    -- DEBUG (nls, nls')  = (litLength fi , litLength fi')
    -- DEBUG (nqs, nqs')  = (qLength   fi , qLength fi')
    -- DEBUG cLength      = M.size . cm
    -- DEBUG wLength      = length . ws
    -- DEBUG beLength     = length . bindEnvToList . bs
    -- DEBUG litLength    = length . toListSEnv . lits
    -- DEBUG qLength      = length . quals

<<<<<<< HEAD
---------------------------------------------------------------------------
-- | Native Haskell Solver ------------------------------------------------
---------------------------------------------------------------------------
solveNative :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solveNative !cfg !fi0 = do
  -- writeLoud $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  -- rnf fi0 `seq` donePhase Loud "Read Constraints"
  let fi1  = fi0 { quals = remakeQual <$> quals fi0 }
  let si   = {-# SCC "convertFormat" #-} convertFormat fi1
  -- writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si)
  -- rnf si `seq` donePhase Loud "Format Conversion"
  let Right si' = {-# SCC "validate" #-} validate cfg  $!! si
  -- writeLoud $ "fq file after validate: \n" ++ render (toFixpoint cfg si')
  -- rnf si' `seq` donePhase Loud "Validated Constraints"
=======
solveNativeWithFInfo :: (NFData a, Fixpoint a) => Config -> FInfo a -> IO (Result a)
solveNativeWithFInfo !cfg !fi = do
  writeLoud $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  rnf fi `seq` donePhase Loud "Read Constraints"
  let fi' = fi { quals = remakeQual <$> quals fi }
  let si  = {-# SCC "convertFormat" #-} convertFormat fi'
  writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si)
  rnf si `seq` donePhase Loud "Format Conversion"
  let si' = {-# SCC "sanitize" #-} sanitize $!! si
  writeLoud $ "fq file after sanitize: \n" ++ render (toFixpoint cfg si')
  rnf si' `seq` donePhase Loud "Sanitized Constraints"
>>>>>>> master
  when (elimStats cfg) $ printElimStats (deps si')
  let si''  = {-# SCC "renameAll" #-} renameAll $!! si'
  -- writeLoud $ "fq file after uniqify: \n" ++ render (toFixpoint cfg si'')
  -- rnf si'' `seq` donePhase Loud "Uniqify"
  (s0, si''') <- {-# SCC "elim" #-} elim cfg $!! si''
  Result stat soln <- {-# SCC "S.solve" #-} S.solve cfg s0 $!! si'''
  -- rnf soln `seq` donePhase Loud "Solve2"
  let stat' = sid <$> stat
  -- writeLoud $ "\nSolution:\n"  ++ showpp soln
  -- colorStrLn (colorResult stat') (show stat')
  return    $ Result (WrapC . mlookup (cm fi0) . mfromJust "WAT" <$> stat') soln

printElimStats :: Deps -> IO ()
printElimStats d = putStrLn $ printf "KVars (Total/Post-Elim) = (%d, %d) \n" total postElims
  where
    total        = postElims + length (depNonCuts d)
    postElims    = length $ depCuts d

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
       return     $ Result (WrapC <$> x') y

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
  putStrLn $ "Saving Binary File: " ++ file ++ "\n"
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
progressInitFI :: FInfo a -> IO ()
---------------------------------------------------------------------------
progressInitFI = progressInit . fromIntegral . gSccs . cGraph
