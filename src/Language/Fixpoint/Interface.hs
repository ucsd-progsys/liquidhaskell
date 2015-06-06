-- | This module implements the top-level API for interfacing with Fixpoint
--   In particular it exports the functions that solve constraints supplied
--   either as .fq files or as FInfo.

module Language.Fixpoint.Interface (

    -- * Containing Constraints
    FInfo (..)

    -- * Invoke Solver on an FInfo
  , solve

    -- * Invoke Solver on a .fq file
  , solveFQ

    -- * Function to determine outcome
  , resultExit

    -- * Parse Qualifiers from File
  , parseFInfo
) where

import           Data.Functor
-- import           Data.Hashable
import qualified Data.HashMap.Strict              as M
import           Data.List
import           Data.Monoid (mconcat, mempty)
-- import           System.Directory                 (getTemporaryDirectory)
import           System.Exit
-- import           System.FilePath                  ((</>))
import           System.IO                        (IOMode (..), hPutStr,
                                                   withFile)
import           Text.Printf

import           Language.Fixpoint.Solver.Eliminate (eliminateAll)
import           Language.Fixpoint.Solver.Uniqify   (renameAll)
import qualified Language.Fixpoint.Solver.Solve  as S
import           Language.Fixpoint.Config
import           Language.Fixpoint.Files
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Statistics     (statistics)
import           Language.Fixpoint.Parse          (rr, rr')
import           Language.Fixpoint.Types          hiding (kuts, lits)
import           Language.Fixpoint.Errors (exit)
import           Language.Fixpoint.PrettyPrint (showpp)
-- import           System.Console.CmdArgs.Default
import           System.Console.CmdArgs.Verbosity
import           Text.PrettyPrint.HughesPJ


---------------------------------------------------------------------------
-- | Solve FInfo system of horn-clause constraints ------------------------
---------------------------------------------------------------------------
solve :: (Fixpoint a) => Config -> FInfo a -> IO (Result a)
solve cfg x = do
  when (stats cfg) $ statistics cfg x
  case () of
    _ | native cfg -> S.solve  cfg x
    _              -> solveExt cfg x

---------------------------------------------------------------------------
-- | Solve .fq File -------------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg
  | native cfg = solveNative cfg
  | otherwise  = solveFile   cfg


---------------------------------------------------------------------------
-- | Native Haskell Solver
---------------------------------------------------------------------------
solveNative :: Config -> IO ExitCode
solveNative cfg = exit (ExitFailure 2) $ do
  let file  = inFile cfg
  str      <- readFile file
  let fi    = rr' file str :: FInfo ()
  fi'      <- if eliminate cfg then renameAndEliminate cfg fi else return fi
  (res, s) <- S.solve cfg fi'
  let res'  = sid <$> res
  putStrLn  $ "Solution:\n" ++ showpp s
  putStrLn  $ "Result: "    ++ show res'
  return    $ resultExit res'

renameAndEliminate :: Config -> FInfo () -> IO (FInfo ())
renameAndEliminate cfg fi = do
  whenLoud $ putStrLn $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  let fi' = renameAll fi
  whenLoud $ putStrLn $ "fq file after uniqify: \n" ++ render (toFixpoint cfg fi')
  let fi'' = eliminateAll fi'
  whenLoud $ putStrLn $ "fq file after eliminate: \n" ++ render (toFixpoint cfg fi'')
  return fi''

---------------------------------------------------------------------------
-- | External Ocaml Solver
---------------------------------------------------------------------------
solveExt :: (Fixpoint a) => Config -> FInfo a -> IO (Result a)
solveExt cfg fi =   {-# SCC "Solve"  #-} execFq cfg fn fi
                >>= {-# SCC "exitFq" #-} exitFq fn (cm fi)
  where
    fn          = srcFile cfg

execFq :: (Fixpoint a) => Config -> FilePath -> FInfo a -> IO ExitCode
execFq cfg fn fi
  = do writeFile fq qstr
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPutStr h (render d))
       solveFile $ cfg `withTarget` fq
    where
       fq   = extFileName Fq fn
       d    = {-# SCC "FixPointify" #-} toFixpoint cfg fi
       qstr = render (vcat (toFix <$> quals fi) $$ text "\n")

solveFile :: Config -> IO ExitCode
solveFile cfg
  = do fp  <- getFixpointPath
       z3  <- getZ3LibPath
       v   <- (\b -> if b then "-v 1" else "") <$> isLoud
       {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ fixCommand cfg fp z3 v

fixCommand cfg fp z3 verbosity
  = printf "LD_LIBRARY_PATH=%s %s %s %s -notruekvars -refinesort -nosimple -strictsortcheck -sortedquals %s"
           z3 fp verbosity rf (command cfg)
  where
     rf  = if real cfg then realFlags else ""

realFlags :: String
realFlags =  "-no-uif-multiply "
          ++ "-no-uif-divide "

exitFq _ _ (ExitFailure n) | n /= 1
  = return (Crash [] "Unknown Error", M.empty)
exitFq fn cm _
  = do str <- {-# SCC "readOut" #-} readFile (extFileName Out fn)
       let (x, y) = parseFixpointOutput str -- {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)
       return  $ (plugC cm x, y)
    where
       plugC = fmap . mlookup

parseFixpointOutput :: String -> (FixResult Integer, FixSolution)
parseFixpointOutput str = {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)

sanitizeFixpointOutput
  = unlines
  . filter (not . ("//"     `isPrefixOf`))
  . chopAfter ("//QUALIFIERS" `isPrefixOf`)
  . lines

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
                  , gs    = gs     fi }

