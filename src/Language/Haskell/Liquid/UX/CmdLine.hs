{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE MultiWayIf                #-}
{-# LANGUAGE ViewPatterns              #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wwarn=deprecations #-}
{-# OPTIONS_GHC -fno-cse #-}

-- | This module contains all the code needed to output the result which
--   is either: `SAFE` or `WARNING` with some reasonable error message when
--   something goes wrong. All forms of errors/exceptions should go through
--   here. The idea should be to report the error, the source position that
--   causes it, generate a suitable .json file and then exit.

module Language.Haskell.Liquid.UX.CmdLine (
   -- * Get Command Line Configuration
     getOpts, mkOpts, defConfig, config

   -- * Update Configuration With Pragma
   , withPragmas

   -- * Canonicalize Paths in Config
   , canonicalizePaths

   -- * Exit Function
   , exitWithResult
   , addErrors

   -- * Reporting the output of the checking
   , OutputResult(..)
   , reportResult

   -- * Diff check mode
   , diffcheck

   -- * Show info about this version of LiquidHaskell
   , printLiquidHaskellBanner

) where

import Prelude hiding (error)


import Control.Monad
import Control.Monad.IO.Class
import Data.Maybe
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy.Char8 as B
import Development.GitRev (gitCommitCount)
import qualified Paths_liquidhaskell as Meta
import System.Directory
import System.Exit
import System.Environment
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Implicit     hiding (Loud)
import qualified System.Console.CmdArgs.Verbosity as CmdArgs
import System.Console.CmdArgs.Text
import GitHash

import Data.List                           (nub)


import System.FilePath                     (isAbsolute, takeDirectory, (</>))

import qualified Language.Fixpoint.Types.Config as FC
import Language.Fixpoint.Misc
import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types             hiding (panic, Error, Result, saveQuery)
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Solver.Stats as Solver
import Language.Haskell.Liquid.UX.Annotate
import Language.Haskell.Liquid.UX.Config
import Language.Haskell.Liquid.UX.SimpleVersion (simpleVersion)
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types.PrettyPrint ()
import Language.Haskell.Liquid.Types       hiding (typ)
import qualified Language.Haskell.Liquid.UX.ACSS as ACSS

import qualified Language.Haskell.Liquid.GHC.API as GHC
import           Language.Haskell.TH.Syntax.Compat (fromCode, toCode)

import Text.PrettyPrint.HughesPJ           hiding (Mode, (<>))



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
  loggingVerbosity
    = enum [ Quiet        &= name "quiet"   &= help "Minimal logging verbosity"
           , Normal       &= name "normal"  &= help "Normal logging verbosity"
           , CmdArgs.Loud &= name "verbose" &= help "Verbose logging"
           ]

 , files
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

 , nopositivity
    = def
          &= help "Disable Data Type Positivity Check"
          &= name "no-positivity-check"

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

 , bscope
    = def &= help "scope of the outer binders on the inner refinements"
          &= name "bscope"

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

  , oldPLE
    = def
        &= help "Enable Proof-by-Logical-Evaluation"
        &= name "oldple"

  , noInterpreter
    = def
        &= help "Don't use an interpreter to assist PLE in solving constraints"
        &= name "no-interpreter"

  , proofLogicEvalLocal
    = def
        &= help "Enable Proof-by-Logical-Evaluation locally, per function"
        &= name "ple-local"

  , extensionality
    = def
        &= help "Enable extensional interpretation of function equality"
        &= name "extensionality"

  , nopolyinfer
    = def
        &= help "No inference of polymorphic type application. Gives imprecision, but speedup."
        &= name "fast"

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
  , typeclass
    = def
        &= help "Enable Typeclass"
        &= name "typeclass"
  , auxInline
    = def
        &= help "Enable inlining of class methods"
        &= name "aux-inline"
  , maxMatchDepth
    = def
        &= name "max-match-depth"
        &= help "Define the number of expressions to pattern match on (typed-holes must be on to use this flag)."
  , maxAppDepth
    = def
        &= name "max-app-depth"
  , maxArgsDepth
    = def
        &= name "max-args-depth"
  ,
    rwTerminationCheck
    = def
        &= name "rw-termination-check"
        &= help (   "Enable the rewrite divergence checker. "
                 ++ "Can speed up verification if rewriting terminates, but can also cause divergence."
                )
  ,
    skipModule
    = def
        &= name "skip-module"
        &= help "Completely skip this module, don't even compile any specifications in it."
  ,
    noLazyPLE
    = def
        &= name "no-lazy-ple"
        &= help "Don't use Lazy PLE"

  , fuel
    = Nothing
        &= help "Maximum fuel (per-function unfoldings) for PLE"

  , environmentReduction
    = def
        &= explicit
        &= name "environment-reduction"
        &= help "perform environment reduction (disabled by default)"
  , noEnvironmentReduction
    = def
        &= explicit
        &= name "no-environment-reduction"
        &= help "Don't perform environment reduction"
  , inlineANFBindings
    = False
        &= explicit
        &= name "inline-anf-bindings"
        &= help (unwords
          [ "Inline ANF bindings."
          , "Sometimes improves performance and sometimes worsens it."
          , "Disabled by --no-environment-reduction"
          ])
  , pandocHtml
    = False
      &= name "pandoc-html"
      &= help "Use pandoc to generate html."
  } &= program "liquid"
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
  setVerbosity (loggingVerbosity cfg)
  when (json cfg) $ setVerbosity Quiet
  withSmtSolver cfg

-- | Shows the LiquidHaskell banner, that includes things like the copyright, the
-- git commit and the version.
printLiquidHaskellBanner :: IO ()
printLiquidHaskellBanner = whenNormal $ putStrLn copyright

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
  cfg' <- canonicalizePaths pwd cfg
  return $ canonConfig cfg'

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
    l       = safeSourcePos "ENVIRONMENT" 1 1

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
    giTry :: Either String GitInfo
    giTry  = $$(fromCode (toCode tGitInfoCwdTry))
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
withPragmas :: MonadIO m => Config -> FilePath -> [Located String] -> (Config -> m a) -> m a
--------------------------------------------------------------------------------
withPragmas cfg fp ps action
  = do cfg' <- liftIO $ foldM withPragma cfg ps >>= canonicalizePaths fp >>= (return . canonConfig)
       -- As the verbosity is set /globally/ via the cmdargs lib, re-set it.
       liftIO $ setVerbosity (loggingVerbosity cfg')
       res <- action cfg'
       liftIO $ setVerbosity (loggingVerbosity cfg) -- restore the original verbosity.
       pure res


withPragma :: Config -> Located String -> IO Config
withPragma c s = withArgs [val s] $ cmdArgsRun
          config { modeValue = (modeValue config) { cmdArgsValue = c } }

parsePragma   :: Located String -> IO Config
parsePragma = withPragma defConfig

defConfig :: Config
defConfig = Config
  { loggingVerbosity         = Quiet
  , files                    = def
  , idirs                    = def
  , fullcheck                = def
  , linear                   = def
  , stringTheory             = def
  , higherorder              = def
  , smtTimeout               = def
  , higherorderqs            = def
  , diffcheck                = def
  , saveQuery                = def
  , checks                   = def
  , nostructuralterm         = def
  , noCheckUnknown           = def
  , notermination            = False
  , nopositivity             = False
  , rankNTypes               = False
  , noclasscheck             = False
  , gradual                  = False
  , bscope                   = False
  , gdepth                   = 1
  , ginteractive             = False
  , totalHaskell             = def -- True
  , nowarnings               = def
  , noannotations            = def
  , checkDerived             = False
  , caseExpandDepth          = 2
  , notruetypes              = def
  , nototality               = False
  , pruneUnsorted            = def
  , exactDC                  = def
  , noADT                    = def
  , cores                    = def
  , minPartSize              = FC.defaultMinPartSize
  , maxPartSize              = FC.defaultMaxPartSize
  , maxParams                = defaultMaxParams
  , smtsolver                = def
  , shortNames               = def
  , shortErrors              = def
  , cabalDir                 = def
  , ghcOptions               = def
  , cFiles                   = def
  , port                     = defaultPort
  , scrapeInternals          = False
  , scrapeImports            = False
  , scrapeUsedImports        = False
  , elimStats                = False
  , elimBound                = Nothing
  , json                     = False
  , counterExamples          = False
  , timeBinds                = False
  , untidyCore               = False
  , eliminate                = FC.Some
  , noPatternInline          = False
  , noSimplifyCore           = False
  -- PLE-OPT , autoInstantiate   = def
  , noslice                  = False
  , noLiftedImport           = False
  , proofLogicEval           = False
  , oldPLE                   = False
  , noInterpreter            = False
  , proofLogicEvalLocal      = False
  , reflection               = False
  , extensionality           = False
  , nopolyinfer              = False
  , compileSpec              = False
  , noCheckImports           = False
  , typedHoles               = False
  , typeclass                = False
  , auxInline                = False
  , maxMatchDepth            = 4
  , maxAppDepth              = 2
  , maxArgsDepth             = 1
  , rwTerminationCheck       = False
  , skipModule               = False
  , noLazyPLE                = False
  , fuel                     = Nothing
  , environmentReduction     = False
  , noEnvironmentReduction   = False
  , inlineANFBindings        = False
  , pandocHtml               = False
  }


-- | Writes the annotations (i.e. the files in the \".liquid\" hidden folder) and report the result
-- of the checking using a supplied function.
reportResult :: MonadIO m
             => (OutputResult -> m ())
             -> Config
             -> [FilePath]
             -> Output Doc
             -> m ()
reportResult logResultFull cfg targets out = do
  annm <- {-# SCC "annotate" #-} liftIO $ annotate cfg targets out
  liftIO $ whenNormal $ donePhase Loud "annotate"
  if | json cfg  -> liftIO $ reportResultJson annm
     | otherwise -> do
         let r = o_result out
         liftIO $ writeCheckVars $ o_vars out
         cr <- liftIO $ resultWithContext r
         let outputResult = resDocs tidy cr
         -- For now, always print the \"header\" with colours, irrespective to the logger
         -- passed as input.
         -- liftIO $ printHeader (colorResult r) (orHeader outputResult)
         logResultFull outputResult
  pure ()
  where
    tidy :: F.Tidy
    tidy = if shortErrors cfg then F.Lossy else F.Full

    _printHeader :: Moods -> Doc -> IO ()
    _printHeader mood d = colorPhaseLn mood "" (render d)


------------------------------------------------------------------------
exitWithResult :: Config -> [FilePath] -> Output Doc -> IO ()
------------------------------------------------------------------------
exitWithResult cfg = reportResult writeResultStdout cfg

reportResultJson :: ACSS.AnnMap -> IO ()
reportResultJson annm = do
  putStrLn "LIQUID"
  B.putStrLn . encode . annErrors $ annm

resultWithContext :: F.FixResult UserError -> IO (FixResult CError)
resultWithContext (F.Unsafe s es)  = F.Unsafe s    <$> errorsWithContext es
resultWithContext (F.Crash  es s)  = (`F.Crash` s) <$> errorsWithContext es
resultWithContext (F.Safe   stats) = return (F.Safe stats)

instance Show (CtxError Doc) where
  show = showpp

writeCheckVars :: Symbolic a => Maybe [a] -> IO ()
writeCheckVars _ {- Nothing -}    = return ()
--XXX(matt.walker): revert!
-- writeCheckVars (Just [])   = colorPhaseLn Loud "Checked Binders: None" ""
-- writeCheckVars (Just ns)   = colorPhaseLn Loud "Checked Binders:" ""
--                           >> forM_ ns (putStrLn . symbolString . dropModuleNames . symbol)

type CError = CtxError Doc

data OutputResult = OutputResult {
    orHeader :: Doc
    -- ^ The \"header\" like \"LIQUID: SAFE\", or \"LIQUID: UNSAFE\".
  , orMessages :: [(GHC.SrcSpan, Doc)]
    -- ^ The list of pretty-printable messages (typically errors) together with their
    -- source locations.
  }

-- | Writes the result of this LiquidHaskell run to /stdout/.
writeResultStdout :: OutputResult -> IO ()
writeResultStdout (orMessages -> messages) = do
  forM_ messages $ \(sSpan, doc) -> putStrLn (render $ mkErrorDoc sSpan doc {- pprint sSpan <> (text ": error: " <+> doc)-})

mkErrorDoc :: PPrint a => a -> Doc -> Doc
mkErrorDoc sSpan doc =
  -- Gross on screen, nice for Ghcid
  -- pprint sSpan <> (text ": error: " <+> doc)

  -- Nice on screen, invisible in Ghcid ...
  (pprint sSpan <> text ": error: ") $+$ (nest 4 doc)


-- | Given a 'FixResult' parameterised over a 'CError', this function returns the \"header\" to show to
-- the user (i.e. \"SAFE\" or \"UNSAFE\") plus a list of 'Doc's together with the 'SrcSpan' they refer to.
resDocs :: F.Tidy -> F.FixResult CError -> OutputResult
resDocs _ (F.Safe  stats) =
  OutputResult {
    orHeader   = text $ "LIQUID: SAFE (" <> show (Solver.numChck stats) <> " constraints checked)"
  , orMessages = mempty
  }
resDocs _k (F.Crash [] s)  =
  OutputResult {
    orHeader = text "LIQUID: ERROR"
  , orMessages = [(GHC.noSrcSpan, text s)]
  }
resDocs k (F.Crash xs s)  =
  OutputResult {
    orHeader = text "LIQUID: ERROR" <+> text s
  , orMessages = map (cErrToSpanned k . errToFCrash) xs
  }
resDocs k (F.Unsafe _ xs)   =
  OutputResult {
    orHeader   = text "LIQUID: UNSAFE"
  , orMessages = map (cErrToSpanned k) (nub xs)
  }

-- | Renders a 'CError' into a 'Doc' and its associated 'SrcSpan'.
cErrToSpanned :: F.Tidy -> CError -> (GHC.SrcSpan, Doc)
cErrToSpanned k CtxError{ctErr} = (pos ctErr, pprintTidy k ctErr)

errToFCrash :: CtxError a -> CtxError a
errToFCrash ce = ce { ctErr    = tx $ ctErr ce}
  where
    tx (ErrSubType l m _ g t t') = ErrFCrash l m g t t'
    tx e                       = e

{-
   TODO: Never used, do I need to exist?
reportUrl = text "Please submit a bug report at: https://github.com/ucsd-progsys/liquidhaskell" -}

addErrors :: FixResult a -> [a] -> FixResult a
addErrors r []               = r
addErrors (Safe s) errs'      = Unsafe s errs'
addErrors (Unsafe s xs) errs' = Unsafe s (xs ++ errs')
addErrors r  _               = r

instance Fixpoint (F.FixResult CError) where
  toFix = vcat . map snd . orMessages . resDocs F.Full
