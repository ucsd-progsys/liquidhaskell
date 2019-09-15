{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# OPTIONS_GHC -fno-cse #-}

-- | This module contains all the code needed to output the result which
--   is either: `SAFE` or `WARNING` with some reasonable error message when
--   something goes wrong. All forms of errors/exceptions should go through
--   here. The idea should be to report the error, the source position that
--   causes it, generate a suitable .json file and then exit.

module Language.Haskell.Liquid.UX.CmdLine (
   -- * Get Command Line Configuration
     getOpts, mkOpts, defConfig

   -- * Update Configuration With Pragma
   , withPragmas

   -- * Canonicalize Paths in Config
   , canonicalizePaths

   -- * Exit Function
   , exitWithResult
   , addErrors

   -- * Diff check mode
   , diffcheck

) where

import Prelude hiding (error)


import Control.Monad
import Data.Maybe
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy.Char8 as B
import Development.GitRev (gitCommitCount)
import Options.Applicative.Simple (simpleVersion)
import qualified Paths_liquidhaskell as Meta
import System.Directory
import System.Exit
import System.Environment
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Implicit     hiding (Loud)
import System.Console.CmdArgs.Text
import GitHash 

import Data.List                           (nub)


import System.FilePath                     (isAbsolute, takeDirectory, (</>))

import qualified Language.Fixpoint.Types.Config as FC
import Language.Fixpoint.Misc
import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types             hiding (panic, Error, Result, saveQuery)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.UX.Annotate
import Language.Haskell.Liquid.UX.Config
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types.PrettyPrint
import Language.Haskell.Liquid.Types       hiding (typ)
import qualified Language.Haskell.Liquid.UX.ACSS as ACSS


import Text.Parsec.Pos                     (newPos)
import Text.PrettyPrint.HughesPJ           hiding (Mode)



---------------------------------------------------------------------------------
-- Config Magic Numbers----------------------------------------------------------
---------------------------------------------------------------------------------

defaultMaxParams :: Int
defaultMaxParams = 2

---------------------------------------------------------------------------------
-- Parsing Command Line----------------------------------------------------------
---------------------------------------------------------------------------------
config :: Mode (CmdArgs Config)
config = cmdArgsMode $ Config {
   files
    = def &= typ "TARGET"
          &= args
          &= typFile

 , idirs
    = def &= typDir
          &= help "Paths to Spec Include Directory "

 , fullcheck
     = def
           &= help "Full Checking: check all binders (DEFAULT)"

 , diffcheck
    = def
          &= help "Incremental Checking: only check changed binders"

 , higherorder
    = def
          &= help "Allow higher order binders into the logic"

 , smtTimeout 
    = def
          &= help "Timeout of smt queries in msec"    
      
 , higherorderqs
    = def
          &= help "Allow higher order qualifiers to get automatically instantiated"

 , linear
    = def
          &= help "Use uninterpreted integer multiplication and division"

 , stringTheory
    = def
          &= help "Interpretation of Strings by z3"

 , saveQuery
    = def &= help "Save fixpoint query to file (slow)"

 , checks
    = def &= help "Check a specific (top-level) binder"
          &= name "check-var"

 , pruneUnsorted
    = def &= help "Disable prunning unsorted Predicates"
          &= name "prune-unsorted"

 , notermination
    = def 
          &= help "Disable Termination Check"
          &= name "no-termination-check"

 , rankNTypes 
    = def &= help "Adds precise reasoning on presence of rankNTypes"
          &= name "rankNTypes" 

 , noclasscheck
    = def 
          &= help "Disable Class Instance Check"
          &= name "no-class-check"

 , nostructuralterm
    = def &= name "no-structural-termination"
          &= help "Disable structural termination check" 
          
 , gradual
    = def &= help "Enable gradual refinement type checking"
          &= name "gradual"

 , gdepth
    = 1
    &= help ("Size of gradual conretizations, 1 by default")
    &= name "gradual-depth"

 , ginteractive
    = def &= help "Interactive Gradual Solving"
          &= name "ginteractive"

 , totalHaskell
    = def &= help "Check for termination and totality; overrides no-termination flags"
          &= name "total-Haskell"

 , nowarnings
    = def &= help "Don't display warnings, only show errors"
          &= name "no-warnings"

 , noannotations
    = def &= help "Don't create intermediate annotation files"
          &= name "no-annotations"

 , checkDerived
    = def &= help "Check GHC generated binders (e.g. Read, Show instances)"
          &= name "check-derived"

 , caseExpandDepth 
    = 2   &= help "Maximum depth at which to expand DEFAULT in case-of (default=2)"
          &= name "max-case-expand"

 , strata
    = def &= help "Enable Strata Analysis"

 , notruetypes
    = def &= help "Disable Trueing Top Level Types"
          &= name "no-true-types"

 , nototality
    = def &= help "Disable totality check"
          &= name "no-totality"

 , cores
    = def &= help "Use m cores to solve logical constraints"

 , minPartSize
    = FC.defaultMinPartSize
    &= help "If solving on multiple cores, ensure that partitions are of at least m size"

 , maxPartSize
    = FC.defaultMaxPartSize
    &= help ("If solving on multiple cores, once there are as many partitions " ++
             "as there are cores, don't merge partitions if they will exceed this " ++
             "size. Overrides the minpartsize option.")

 , smtsolver
    = def &= help "Name of SMT-Solver"

 , noCheckUnknown
    = def &= explicit
          &= name "no-check-unknown"
          &= help "Don't complain about specifications for unexported and unused values "

 , maxParams
    = defaultMaxParams &= help "Restrict qualifier mining to those taking at most `m' parameters (2 by default)"

 , shortNames
    = def &= name "short-names"
          &= help "Print shortened names, i.e. drop all module qualifiers."

 , shortErrors
    = def &= name "short-errors"
          &= help "Don't show long error messages, just line numbers."

 , cabalDir
    = def &= name "cabal-dir"
          &= help "Find and use .cabal to add paths to sources for imported files"

 , ghcOptions
    = def &= name "ghc-option"
          &= typ "OPTION"
          &= help "Pass this option to GHC"

 , cFiles
    = def &= name "c-files"
          &= typ "OPTION"
          &= help "Tell GHC to compile and link against these files"

 , port
     = defaultPort
          &= name "port"
          &= help "Port at which lhi should listen"

 , exactDC
    = def &= help "Exact Type for Data Constructors"
          &= name "exact-data-cons"

 , noADT
    = def &= help "Do not generate ADT representations in refinement logic"
          &= name "no-adt"

 , scrapeImports
    = False &= help "Scrape qualifiers from imported specifications"
            &= name "scrape-imports"
            &= explicit

 , scrapeInternals
    = False &= help "Scrape qualifiers from auto generated specifications"
            &= name "scrape-internals"
            &= explicit

 , scrapeUsedImports
    = False &= help "Scrape qualifiers from used, imported specifications"
            &= name "scrape-used-imports"
            &= explicit

 , elimStats
    = False &= name "elimStats"
            &= help "Print eliminate stats"

 , elimBound
    = Nothing
            &= name "elimBound"
            &= help "Maximum chain length for eliminating KVars"

 , noslice
    = False
            &= name "noSlice"
            &= help "Disable non-concrete KVar slicing"

 , noLiftedImport
    = False
            &= name "no-lifted-imports"
            &= help "Disable loading lifted specifications (for legacy libs)"

 , json
    = False &= name "json"
            &= help "Print results in JSON (for editor integration)"

 , counterExamples
    = False &= name "counter-examples"
            &= help "Attempt to generate counter-examples to type errors (experimental!)"

 , timeBinds
    = False &= name "time-binds"
            &= help "Solve each (top-level) asserted type signature separately & time solving."

  , untidyCore
    = False &= name "untidy-core"
            &= help "Print fully qualified identifier names in verbose mode"

  , eliminate
    = FC.Some
            &= name "eliminate"
            &= help "Use elimination for 'all' (use TRUE for cut-kvars), 'some' (use quals for cut-kvars) or 'none' (use quals for all kvars)."

  , noPatternInline
    = False &= name "no-pattern-inline"
            &= help "Don't inline special patterns (e.g. `>>=` and `return`) during constraint generation."

  , noSimplifyCore
    = False &= name "no-simplify-core"
            &= help "Don't simplify GHC core before constraint generation"

  -- PLE-OPT , autoInstantiate
    -- PLE-OPT = def
          -- PLE-OPT &= help "How to instantiate axiomatized functions `smtinstances` for SMT instantiation, `liquidinstances` for terminating instantiation"
          -- PLE-OPT &= name "automatic-instances"

  , proofLogicEval
    = def  
        &= help "Enable Proof-by-Logical-Evaluation"
        &= name "ple"

  , proofLogicEvalLocal
    = def  
        &= help "Enable Proof-by-Logical-Evaluation locally, per function"
        &= name "ple-local"


  , reflection 
    = def 
        &= help "Enable reflection of Haskell functions and theorem proving" 
        &= name "reflection"

  , compileSpec 
    = def 
        &= name "compile-spec"
        &= help "Only compile specifications (into .bspec file); skip verification" 

  , noCheckImports
    = def 
        &= name "no-check-imports"
        &= help "Do not check the transitive imports; only check the target files." 

  , typedHoles
    = def 
        &= name "typed-holes"
        &= help "Use (refinement) typed-holes [currently warns on '_x' variables]"
  } &= verbosity
    &= program "liquid"
    &= help    "Refinement Types for Haskell"
    &= summary copyright
    &= details [ "LiquidHaskell is a Refinement Type based verifier for Haskell"
               , ""
               , "To check a Haskell file foo.hs, type:"
               , "  liquid foo.hs "
               ]

defaultPort :: Int
defaultPort = 3000

getOpts :: [String] -> IO Config
getOpts as = do
  cfg0   <- envCfg
  cfg1   <- mkOpts =<< cmdArgsRun'
                         config { modeValue = (modeValue config)
                                                { cmdArgsValue   = cfg0
                                                }
                                }
                         as
  cfg    <- fixConfig cfg1
  when (json cfg) $ setVerbosity Quiet
  whenNormal $ putStrLn copyright
  withSmtSolver cfg


cmdArgsRun' :: Mode (CmdArgs a) -> [String] -> IO a
cmdArgsRun' md as
  = case parseResult of
      Left e  -> putStrLn (helpMsg e) >> exitFailure
      Right a -> cmdArgsApply a
    where
      helpMsg e = showText defaultWrap $ helpText [e] HelpFormatDefault md
      parseResult = process md (wideHelp as)
      wideHelp = map (\a -> if a == "--help" || a == "-help" then "--help=120" else a)


--------------------------------------------------------------------------------
withSmtSolver :: Config -> IO Config
--------------------------------------------------------------------------------
withSmtSolver cfg =
  case smtsolver cfg of
    Just smt -> do found <- findSmtSolver smt
                   case found of
                     Just _ -> return cfg
                     Nothing -> panic Nothing (missingSmtError smt)
    Nothing  -> do smts <- mapM findSmtSolver [FC.Z3, FC.Cvc4, FC.Mathsat]
                   case catMaybes smts of
                     (s:_) -> return (cfg {smtsolver = Just s})
                     _     -> panic Nothing noSmtError
  where
    noSmtError = "LiquidHaskell requires an SMT Solver, i.e. z3, cvc4, or mathsat to be installed."
    missingSmtError smt = "Could not find SMT solver '" ++ show smt ++ "'. Is it on your PATH?"

findSmtSolver :: FC.SMTSolver -> IO (Maybe FC.SMTSolver)
findSmtSolver smt = maybe Nothing (const $ Just smt) <$> findExecutable (show smt)

fixConfig :: Config -> IO Config
fixConfig cfg = do
  pwd <- getCurrentDirectory
  cfg <- canonicalizePaths pwd cfg
  return $ canonConfig cfg

-- | Attempt to canonicalize all `FilePath's in the `Config' so we don't have
--   to worry about relative paths.
canonicalizePaths :: FilePath -> Config -> IO Config
canonicalizePaths pwd cfg = do
  tgt   <- canonicalizePath pwd
  isdir <- doesDirectoryExist tgt
  is    <- mapM (canonicalize tgt isdir) $ idirs cfg
  cs    <- mapM (canonicalize tgt isdir) $ cFiles cfg
  return $ cfg { idirs = is, cFiles = cs }

canonicalize :: FilePath -> Bool -> FilePath -> IO FilePath
canonicalize tgt isdir f
  | isAbsolute f = return f
  | isdir        = canonicalizePath (tgt </> f)
  | otherwise    = canonicalizePath (takeDirectory tgt </> f)

envCfg :: IO Config
envCfg = do
  so <- lookupEnv "LIQUIDHASKELL_OPTS"
  case so of
    Nothing -> return defConfig
    Just s  -> parsePragma $ envLoc s
  where
    envLoc  = Loc l l
    l       = newPos "ENVIRONMENT" 0 0

copyright :: String
copyright = concat $ concat
  [ ["LiquidHaskell "]
  , [$(simpleVersion Meta.version)]
  , [gitInfo]
  -- , [" (" ++ _commitCount ++ " commits)" | _commitCount /= ("1"::String) &&
  --                                          _commitCount /= ("UNKNOWN" :: String)]
  , ["\nCopyright 2013-19 Regents of the University of California. All Rights Reserved.\n"]
  ]
  where
    _commitCount = $gitCommitCount

gitInfo :: String
gitInfo  = msg
  where
    giTry  = $$tGitInfoCwdTry
    msg    = case giTry of
               Left _   -> " no git information"
               Right gi -> gitMsg gi
    
gitMsg :: GitInfo -> String
gitMsg gi = concat
  [ " [", giBranch gi, "@", giHash gi
  , " (", giCommitDate gi, ")"
  -- , " (", show (giCommitCount gi), " commits in HEAD)"
  , "] "
  ]


-- [NOTE:searchpath]
-- 1. we used to add the directory containing the file to the searchpath,
--    but this is bad because GHC does NOT do this, and it causes spurious
--    "duplicate module" errors in the following scenario
--      > tree
--      .
--      ├── Bar.hs
--      └── Foo
--          ├── Bar.hs
--          └── Goo.hs
--    If we run `liquid Foo/Goo.hs` and that imports Bar, GHC will not know
--    whether we mean to import Bar.hs or Foo/Bar.hs
-- 2. tests fail if you flip order of idirs'

mkOpts :: Config -> IO Config
mkOpts cfg = do
  let files' = sortNub $ files cfg
  id0       <- getIncludeDir
  return     $ cfg { files       = files'
                                   -- See NOTE [searchpath]
                   , idirs       = [id0 </> gHC_VERSION, id0]
                                ++ idirs cfg
                   }

--------------------------------------------------------------------------------
-- | Updating options
--------------------------------------------------------------------------------
canonConfig :: Config -> Config
canonConfig cfg = cfg
  { diffcheck   = diffcheck cfg && not (fullcheck cfg)
  -- , eliminate   = if higherOrderFlag cfg then FC.All else eliminate cfg
  }

--------------------------------------------------------------------------------
withPragmas :: Config -> FilePath -> [Located String] -> IO Config
--------------------------------------------------------------------------------
withPragmas cfg fp ps
  = foldM withPragma cfg ps >>= canonicalizePaths fp >>= (return . canonConfig)

withPragma :: Config -> Located String -> IO Config
withPragma c s = withArgs [val s] $ cmdArgsRun
          config { modeValue = (modeValue config) { cmdArgsValue = c } }

parsePragma   :: Located String -> IO Config
parsePragma = withPragma defConfig

defConfig :: Config
defConfig = Config 
  { files             = def
  , idirs             = def
  , fullcheck         = def
  , linear            = def
  , stringTheory      = def
  , higherorder       = def
  , smtTimeout        = def 
  , higherorderqs     = def
  , diffcheck         = def
  , saveQuery         = def
  , checks            = def
  , nostructuralterm  = def 
  , noCheckUnknown    = def
  , notermination     = False 
  , rankNTypes        = False 
  , noclasscheck      = False 
  , gradual           = False
  , gdepth            = 1
  , ginteractive      = False
  , totalHaskell      = def -- True 
  , nowarnings        = def
  , noannotations     = def
  , checkDerived      = False
  , caseExpandDepth   = 2 
  , strata            = def
  , notruetypes       = def
  , nototality        = False
  , pruneUnsorted     = def
  , exactDC           = def
  , noADT             = def
  , cores             = def
  , minPartSize       = FC.defaultMinPartSize
  , maxPartSize       = FC.defaultMaxPartSize
  , maxParams         = defaultMaxParams
  , smtsolver         = def
  , shortNames        = def
  , shortErrors       = def
  , cabalDir          = def
  , ghcOptions        = def
  , cFiles            = def
  , port              = defaultPort
  , scrapeInternals   = False
  , scrapeImports     = False
  , scrapeUsedImports = False
  , elimStats         = False
  , elimBound         = Nothing
  , json              = False
  , counterExamples   = False
  , timeBinds         = False
  , untidyCore        = False
  , eliminate         = FC.Some
  , noPatternInline   = False
  , noSimplifyCore    = False
  -- PLE-OPT , autoInstantiate   = def
  , noslice           = False
  , noLiftedImport    = False
  , proofLogicEval    = False
  , proofLogicEvalLocal = False
  , reflection        = False
  , compileSpec       = False
  , noCheckImports    = False
  , typedHoles        = False
  }

------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
exitWithResult :: Config -> [FilePath] -> Output Doc -> IO (Output Doc)
------------------------------------------------------------------------
exitWithResult cfg targets out = do
  annm <- {-# SCC "annotate" #-} annotate cfg targets out
  whenNormal $ donePhase Loud "annotate"
  -- let r = o_result out -- `addErrors` o_errors out
  consoleResult cfg out annm
  return out -- { o_result = r }

consoleResult :: Config -> Output a -> ACSS.AnnMap -> IO ()
consoleResult cfg
  | json cfg  = consoleResultJson cfg
  | otherwise = consoleResultFull cfg

consoleResultFull :: Config -> Output a -> t -> IO ()
consoleResultFull cfg out _ = do
   let r = o_result out
   writeCheckVars $ o_vars out
   cr <- resultWithContext r
   writeResult cfg (colorResult r) cr

consoleResultJson :: t -> t1 -> ACSS.AnnMap -> IO ()
consoleResultJson _ _ annm = do
  putStrLn "RESULT"
  B.putStrLn . encode . annErrors $ annm

resultWithContext :: F.FixResult UserError -> IO (FixResult CError)
resultWithContext (F.Unsafe es)   = F.Unsafe      <$> errorsWithContext es
resultWithContext (F.Crash  es s) = (`F.Crash` s) <$> errorsWithContext es
resultWithContext (F.Safe)        = return F.Safe 

instance Show (CtxError Doc) where
  show = showpp

writeCheckVars :: Symbolic a => Maybe [a] -> IO ()
writeCheckVars Nothing     = return ()
writeCheckVars (Just [])   = colorPhaseLn Loud "Checked Binders: None" ""
writeCheckVars (Just ns)   = colorPhaseLn Loud "Checked Binders:" "" 
                          >> forM_ ns (putStrLn . symbolString . dropModuleNames . symbol)

type CError = CtxError Doc

writeResult :: Config -> Moods -> F.FixResult CError -> IO ()
writeResult cfg c          = mapM_ (writeDoc c) . zip [0..] . resDocs tidy
  where
    tidy                   = if shortErrors cfg then F.Lossy else F.Full
    writeDoc c (i, d)      = writeBlock c i $ lines $ render d
    writeBlock _ _ []      = return ()
    writeBlock c 0 ss      = forM_ ss (colorPhaseLn c "")
    writeBlock _  _ ss     = forM_ ("\n" : ss) putStrLn


resDocs :: F.Tidy -> F.FixResult CError -> [Doc]
resDocs _ F.Safe           = [text "RESULT: SAFE"]
resDocs k (F.Crash xs s)   = text "RESULT: ERROR"  : text s : pprManyOrdered k "" (errToFCrash <$> xs)
resDocs k (F.Unsafe xs)    = text "RESULT: UNSAFE" : pprManyOrdered k "" (nub xs)

errToFCrash :: CtxError a -> CtxError a
errToFCrash ce = ce { ctErr    = tx $ ctErr ce}
  where
    tx (ErrSubType l m g t t') = ErrFCrash l m g t t'
    tx e                       = e

{-
   TODO: Never used, do I need to exist?
reportUrl = text "Please submit a bug report at: https://github.com/ucsd-progsys/liquidhaskell" -}

addErrors :: FixResult a -> [a] -> FixResult a
addErrors r []             = r
addErrors Safe errs        = Unsafe errs
addErrors (Unsafe xs) errs = Unsafe (xs ++ errs)
addErrors r  _             = r

instance Fixpoint (F.FixResult CError) where
  toFix = vcat . resDocs F.Full
