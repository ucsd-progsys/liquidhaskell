
import qualified Language.Fixpoint.Solver.Deps  as D
import qualified Language.Fixpoint.Solver.Solve as S
import Language.Fixpoint.Interface     (solveFile)
import System.Environment              (getArgs)
-- import System.Console.GetOpt
import Language.Fixpoint.Config hiding (config)
import Data.Maybe                      (fromMaybe, listToMaybe)
import System.Exit

import System.Console.CmdArgs
import System.Console.CmdArgs.Verbosity (whenLoud)
import Control.Applicative ((<$>))
import Language.Fixpoint.Parse
import Language.Fixpoint.Types
import Text.PrettyPrint.HughesPJ
import qualified Control.Exception as Ex
import Language.Fixpoint.Errors (exit)

main = do cfg <- getOpts
          whenLoud $ putStrLn $ "Options: " ++ show cfg
          if (native cfg)
            then solveNative' cfg (inFile cfg)
            else solveFile    cfg



config = Config {
    inFile      = def   &= typ "TARGET"       &= args    &= typFile
  , outFile     = "out" &= help "Output file"
  , solver      = def   &= help "Name of SMT Solver"
  , genSorts    = def   &= help "Generalize qualifier sorts"
  , ueqAllSorts = def   &= help "use UEq on all sorts"
  , native      = False &= help "Use (new, non-working) Haskell Solver"
  , real        = False &= help "Experimental support for the theory of real numbers"
  }
  &= verbosity
  &= program "fixpoint"
  &= help    "Predicate Abstraction Based Horn-Clause Solver"
  &= summary "fixpoint Copyright 2009-13 Regents of the University of California."
  &= details [ "Predicate Abstraction Based Horn-Clause Solver"
             , ""
             , "To check a file foo.fq type:"
             , "  fixpoint foo.fq"
             ]

getOpts :: IO Config
getOpts = do md <- cmdArgs config
             putStrLn $ banner md
             return md

banner args =  "Liquid-Fixpoint Copyright 2009-13 Regents of the University of California.\n"
            ++ "All Rights Reserved.\n"

--------------------------------------------------------------
-- | Hook for Haskell Solver ---------------------------------
--------------------------------------------------------------

-- | Fake Dependencies Harness

solveNative :: Config -> FilePath -> IO ExitCode
solveNative cfg file
  = do str     <- readFile file
       let fi   = rr' file str :: FInfo ()
       res     <- D.solve cfg fi
       putStrLn $ "Result: " ++ show res
       error "TODO: solveNative"

-- | Real Haskell Native Solver
solveNative' :: Config -> FilePath -> IO ExitCode
solveNative' cfg file = exit (ExitFailure 2) $ do
  str      <- readFile file
  let fi    = rr' file str :: FInfo ()
  (res, _) <- S.solve cfg fi
  let res'  = sid <$> res
  putStrLn  $ "Result: " ++ show res'
  return      ExitSuccess
