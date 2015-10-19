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

import           Data.Binary
import qualified Data.HashMap.Strict                as M
import           Data.List                          hiding (partition)
import           System.Exit                        (ExitCode (..))
import           System.Console.CmdArgs.Verbosity   hiding (Loud)
import           Text.PrettyPrint.HughesPJ          (render)
import           Text.Printf                        (printf)
import           Control.Monad                      (when, void)

import           Language.Fixpoint.Solver.Validate  (sanitize)
import           Language.Fixpoint.Solver.Eliminate (eliminateAll)
import           Language.Fixpoint.Solver.Deps      (deps, Deps (..))
import           Language.Fixpoint.Solver.Uniqify   (renameAll)
import qualified Language.Fixpoint.Solver.Solve     as S
import           Language.Fixpoint.Solver.Solution  (Solution)
import           Language.Fixpoint.Config           (Config (..), command, withTarget)
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
-- | Solve .fq File -------------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg
  | binary cfg    = saveBinary cfg
  | native cfg    = solveWith cfg (solve    cfg)
  | multicore cfg = solveWith cfg (solvePar cfg)
  | otherwise     = solveFile cfg

multicore :: Config -> Bool
multicore cfg = cores cfg /= Just 1

---------------------------------------------------------------------------
-- | Solve FInfo system of horn-clause constraints ------------------------
---------------------------------------------------------------------------
solve, solve' :: (NFData a, Fixpoint a) => Config -> FInfo a -> IO (Result a)
solve cfg fi      = do when (binary cfg) $ do
                         putStrLn $ "Saving Binary File to: " ++ binaryFile cfg
                         saveBinaryFile cfg fi
                       solve' cfg fi

solve' cfg fi
  | parts cfg     = partition cfg  $!! fi
  | stats cfg     = statistics cfg $!! fi
  | native cfg    = {-# SCC "solveNative" #-} solveNativeWithFInfo cfg $!! fi
  | multicore cfg = solvePar cfg $!! fi
  | otherwise     = solveExt cfg $!! fi

---------------------------------------------------------------------------
-- | Save Query to Binary File
---------------------------------------------------------------------------
saveBinary :: Config -> IO ExitCode
saveBinary cfg
  | isBinary f = return ExitSuccess
  | otherwise  = exit (ExitFailure 2) $ readFInfo f >>=
                                        saveBinaryFile cfg >>
                                        return ExitSuccess
  where
    f          = inFile cfg

saveBinaryFile      :: Config -> FInfo a -> IO ()
saveBinaryFile cfg  = encodeFile (binaryFile cfg) . void

binaryFile :: Config -> FilePath
binaryFile cfg = withExt (srcFile cfg) BinFq

isBinary :: FilePath -> Bool
isBinary = isExtFile BinFq

---------------------------------------------------------------------------
-- | Native Haskell Solver
---------------------------------------------------------------------------
solveWith :: Config -> (FInfo () -> IO (Result ())) -> IO ExitCode
solveWith cfg s = exit (ExitFailure 2) $ do
  fi    <- readFInfo (inFile cfg)
  res   <- s fi
  return $ resultExit (resStatus res)

readFInfo :: FilePath -> IO (FInfo ())
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
  when (elimStats cfg) $ printElimStats (deps si')
  let si''  = {-# SCC "renameAll" #-} renameAll $!! si'
  writeLoud $ "fq file after uniqify: \n" ++ render (toFixpoint cfg si'')
  rnf si'' `seq` donePhase Loud "Uniqify"
  (s0, si''') <- {-# SCC "elim" #-} elim cfg $!! si''
  Result stat soln <- {-# SCC "S.solve" #-} S.solve cfg s0 $!! si'''
  rnf soln `seq` donePhase Loud "Solve"
  let stat' = sid <$> stat
  writeLoud $ "\nSolution:\n"  ++ showpp soln
  -- render (pprintKVs $ hashMapToAscList soln) -- showpp soln
  colorStrLn (colorResult stat') (show stat')
  return    $ Result (WrapC . mlookup (cm fi) . mfromJust "WAT" <$> stat') soln

printElimStats :: Deps -> IO ()
printElimStats d = do
  let postElims = length $ depCuts d
  let total = postElims + length (depNonCuts d)
  putStrLn $ "TOTAL KVars: " ++ show total
          ++ "\nPOST-ELIMINATION KVars: " ++ show postElims

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
-- | External Ocaml Solver
---------------------------------------------------------------------------
solveExt :: (Fixpoint a) => Config -> FInfo a -> IO (Result a)
solveExt cfg fi =   {-# SCC "Solve"  #-} execFq cfg fn fi
                >>= {-# SCC "exitFq" #-} exitFq fn (cm fi)
  where
    fn          = fileName fi -- srcFile cfg

-- | Partitions an FInfo into 1 or more independent parts, then
--   calls solveExt on each in parallel
solvePar :: (Fixpoint a) => Config -> FInfo a -> IO (Result a)
solvePar c fi = do
   mci <- mcInfo c
   let (_, fis) = partition' (Just mci) fi
   writeLoud $ "Number of partitions: " ++ show (length fis)
   writeLoud $ "number of cores: " ++ show (cores c)
   writeLoud $ "minimum part size: " ++ show (minPartSize c)
   writeLoud $ "maximum part size: " ++ show (maxPartSize c)
   case fis of
      [] -> errorstar "partiton' returned empty list!"
      [onePart] -> solveExt c onePart
      _ -> inParallelUsing fis (solveExt c)

execFq :: (Fixpoint a) => Config -> FilePath -> FInfo a -> IO ExitCode
execFq cfg fn fi
  = do writeFile fq $ render $ {-# SCC "FixPointify" #-} toFixpoint cfg fi
       solveFile $ cfg `withTarget` fq
    where
       fq   = extFileName Fq fn

solveFile :: Config -> IO ExitCode
solveFile cfg
  = do fp  <- getFixpointPath
       z3  <- getZ3LibPath
       v   <- (\b -> if b then "-v 1" else "") <$> isLoud
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
