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
  , parseQualifiers
) where

import           Data.Functor
-- import           Data.Hashable
import qualified Data.HashMap.Strict              as M
import           Data.List
-- import           Data.Monoid
-- import           System.Directory                 (getTemporaryDirectory)
import           System.Exit
-- import           System.FilePath                  ((</>))
import           System.IO                        (IOMode (..), hPutStr,
                                                   withFile)
import           Text.Printf

import qualified Language.Fixpoint.Solver.Eliminate   as E
import qualified Language.Fixpoint.Solver.Solve  as S
import           Language.Fixpoint.Config
import           Language.Fixpoint.Files
import           Language.Fixpoint.Misc
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
solve :: Config -> FInfo a -> IO (Result a)
solve cfg
  | native cfg = S.solve  cfg
  | otherwise  = solveExt cfg

---------------------------------------------------------------------------
-- | Solve .fq File -------------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg
  | native cfg = solveNative' cfg
  | otherwise  = solveFile    cfg


---------------------------------------------------------------------------
-- | Fake Dependencies Harness Solver
---------------------------------------------------------------------------
solveNative :: Config -> IO ExitCode
solveNative cfg
  = do let file = inFile cfg
       str     <- readFile file
       let fi   = rr' file str :: FInfo ()
       res     <- E.solve cfg fi
       putStrLn $ "Result: " ++ show res
       error "TODO: solveNative"

---------------------------------------------------------------------------
-- | Native Haskell Solver
---------------------------------------------------------------------------
solveNative' :: Config -> IO ExitCode
solveNative' cfg = exit (ExitFailure 2) $ do
  let file  = inFile cfg
  str      <- readFile file
  let fi    = rr' file str :: FInfo ()
  (res, s) <- S.solve cfg fi
  let res'  = sid <$> res
  putStrLn  $ "Solution:\n" ++ showpp s
  putStrLn  $ "Result: "    ++ show res'
  return    $ resultExit res'

---------------------------------------------------------------------------
-- | External Ocaml Solver
---------------------------------------------------------------------------
solveExt :: Config -> FInfo a -> IO (Result a)
solveExt cfg fi =   {-# SCC "Solve"  #-} execFq cfg fn fi
                >>= {-# SCC "exitFq" #-} exitFq fn (cm fi)
  where
    fn          = srcFile cfg

execFq cfg fn fi
  = do writeFile fq qstr
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPutStr h (render d))
       solveFile $ cfg `withTarget` fq
    where
       fq   = extFileName Fq fn
       d    = {-# SCC "FixPointify" #-} toFixpoint fi
       qstr = render ((vcat $ toFix <$> quals fi) $$ text "\n")

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
parseQualifiers :: [FilePath] -> IO [Qualifier]
---------------------------------------------------------------------------
parseQualifiers = concatMapM parseQF

parseQF :: FilePath -> IO [Qualifier]
parseQF f = do
  str   <- readFile f
  let fi = rr' f str :: FInfo ()
  return $ quals fi

-- OLD CUT USE NEW SMTLIB INTERFACE ---------------------------------------------------------------------------
-- OLD CUT USE NEW SMTLIB INTERFACE -- | One Shot validity query ----------------------------------------------
-- OLD CUT USE NEW SMTLIB INTERFACE ---------------------------------------------------------------------------
-- OLD CUT USE NEW SMTLIB INTERFACE 
-- OLD CUT USE NEW SMTLIB INTERFACE ---------------------------------------------------------------------------
-- OLD CUT USE NEW SMTLIB INTERFACE checkValid :: (Hashable a) => a -> [(Symbol, Sort)] -> Pred -> IO (FixResult a)
-- OLD CUT USE NEW SMTLIB INTERFACE ---------------------------------------------------------------------------
-- OLD CUT USE NEW SMTLIB INTERFACE checkValid n xts p
-- OLD CUT USE NEW SMTLIB INTERFACE   = do file   <- (</> show (hash n)) <$> getTemporaryDirectory
-- OLD CUT USE NEW SMTLIB INTERFACE        (r, _) <- solve def file [] $ validFInfo n xts p
-- OLD CUT USE NEW SMTLIB INTERFACE        return (sinfo <$> r)
-- OLD CUT USE NEW SMTLIB INTERFACE 
-- OLD CUT USE NEW SMTLIB INTERFACE validFInfo         :: a -> [(Symbol, Sort)] -> Pred -> FInfo a
-- OLD CUT USE NEW SMTLIB INTERFACE validFInfo l xts p = FI constrm [] benv emptySEnv [] ksEmpty []
-- OLD CUT USE NEW SMTLIB INTERFACE   where
-- OLD CUT USE NEW SMTLIB INTERFACE     constrm        = M.singleton 0 $ validSubc l ibenv p
-- OLD CUT USE NEW SMTLIB INTERFACE     binds          = [(x, trueSortedReft t) | (x, t) <- xts]
-- OLD CUT USE NEW SMTLIB INTERFACE     ibenv          = insertsIBindEnv bids emptyIBindEnv
-- OLD CUT USE NEW SMTLIB INTERFACE     (bids, benv)   = foldlMap (\e (x,t) -> insertBindEnv x t e) emptyBindEnv binds
-- OLD CUT USE NEW SMTLIB INTERFACE 
-- OLD CUT USE NEW SMTLIB INTERFACE validSubc         :: a -> IBindEnv -> Pred -> SubC a
-- OLD CUT USE NEW SMTLIB INTERFACE validSubc l env p = safeHead "Interface.validSubC" $ subC env PTrue lhs rhs i t l
-- OLD CUT USE NEW SMTLIB INTERFACE   where
-- OLD CUT USE NEW SMTLIB INTERFACE     lhs           = mempty
-- OLD CUT USE NEW SMTLIB INTERFACE     rhs           = RR mempty (predReft p)
-- OLD CUT USE NEW SMTLIB INTERFACE     i             = Just 0
-- OLD CUT USE NEW SMTLIB INTERFACE     t             = []
-- OLD CUT USE NEW SMTLIB INTERFACE 
-- OLD CUT USE NEW SMTLIB INTERFACE result         :: a -> Bool -> FixResult a
-- OLD CUT USE NEW SMTLIB INTERFACE result _ True  = Safe
-- OLD CUT USE NEW SMTLIB INTERFACE result x False = Unsafe [x]
-- OLD CUT USE NEW SMTLIB INTERFACE 
