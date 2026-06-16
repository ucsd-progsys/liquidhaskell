{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE LambdaCase                #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wwarn=deprecations #-}
{-# OPTIONS_GHC -fno-cse #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module contains all the code needed to output the result which
--   is either: `SAFE` or `WARNING` with some reasonable error message when
--   something goes wrong. All forms of errors/exceptions should go through
--   here. The idea should be to report the error, the source position that
--   causes it, generate a suitable .json file and then exit.

module Language.Haskell.Liquid.UX.CmdLine (
   -- * Get Command Line Configuration
     getOpts, defConfig

   -- * Update Configuration With Pragma
   , withPragmas

   -- * Collecting errors
   , addErrors

   -- * Reporting the output of the checking
   , OutputResult(..)
   , reportResult

   -- * Diff check mode
   , diffcheck

) where

import Prelude hiding (error)
import Prelude (error)

import Control.Monad
import Control.Monad.IO.Class
import Data.Char                             (isSpace, toLower)
import Data.Maybe
import Data.Functor                          ((<&>))
import Data.Aeson                            (encode)
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Paths_liquidhaskell_boot as Meta
import System.Console.GetOpt
import qualified Language.Fixpoint.Verbosity as FxV
import System.Directory
import System.Exit
import System.Environment
import GitHash

import Data.List                             (nub, intercalate)

import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Misc as F
import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types               hiding (panic, Error, Result, saveQuery)
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Solver.Stats as Solver
import Language.Haskell.Liquid.UX.Annotate
import Language.Haskell.Liquid.UX.Config
import Language.Haskell.Liquid.UX.SimpleVersion (simpleVersion)
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Types.Errors  hiding (typ)
import Language.Haskell.Liquid.Types.PrettyPrint ()
import Language.Haskell.Liquid.Types.Types
import qualified Language.Haskell.Liquid.UX.ACSS as ACSS

import qualified Liquid.GHC.API as GHC
import           Language.Haskell.TH.Syntax.Compat (fromCode, toCode)

import Text.PrettyPrint.HughesPJ             hiding ((<>))


---------------------------------------------------------------------------------
-- Config Magic Numbers----------------------------------------------------------
---------------------------------------------------------------------------------

defaultMaxParams :: Int
defaultMaxParams = 2

---------------------------------------------------------------------------------
-- Parsing Command Line----------------------------------------------------------
---------------------------------------------------------------------------------

-- | Default configuration: plain Haskell record, no cmdargs annotations.
defConfig :: Config
defConfig = Config
  { loggingVerbosity              = Minimal
  , fullcheck                     = False
  , diffcheck                     = False
  , higherorder                   = False
  , smtTimeout                    = Nothing
  , higherorderqs                 = False
  , linear                        = False
  , stringTheory                  = False
  , saveQuery                     = False
  , saveBfqOnError                = False
  , checks                        = []
  , pruneUnsorted                 = False
  , notermination                 = False
  , nopositivity                  = False
  , rankNTypes                    = False
  , noclasscheck                  = False
  , nostructuralterm              = False
  , bscope                        = False
  , totalHaskell                  = False
  , nowarnings                    = False
  , noannotations                 = False
  , caseExpandDepth               = 2
  , notruetypes                   = False
  , nototality                    = False
  , cores                         = Just 1
  , minPartSize                   = FC.defaultMinPartSize
  , maxPartSize                   = FC.defaultMaxPartSize
  , smtsolver                     = Nothing
  , noCheckUnknown                = False
  , maxParams                     = defaultMaxParams
  , shortNames                    = False
  , shortErrors                   = False
  , adtSpec                       = False
  , expectErrorContaining         = []
  , expectAnyError                = False
  , scrapeInternals               = False
  , elimStats                     = False
  , elimBound                     = Nothing
  , json                          = False
  , counterExamples               = False
  , timeBinds                     = False
  , untidyCore                    = False
  , eliminate                     = FC.Some
  , noPatternInline               = False
  , noSimplifyCore                = False
  , noslice                       = False
  , noLiftedImport                = False
  , proofLogicEval                = False
  , pleWithUndecidedGuards        = False
  , interpreter                   = False
  , proofLogicEvalLocal           = False
  , etabeta                       = False
  , dependantCase                 = False
  , extensionality                = False
  , nopolyinfer                   = False
  , reflection                    = False
  , compileSpec                   = False
  , typeclass                     = False
  , auxInline                     = False
  , rwTerminationCheck            = False
  , skipModule                    = False
  , fuel                          = Nothing
  , environmentReduction          = False
  , noEnvironmentReduction        = False
  , inlineANFBindings             = False
  , pandocHtml                    = False
  , excludeAutomaticAssumptionsFor = []
  , dumpOpaqueReflections         = False
  , dumpPreNormalizedCore         = False
  , dumpNormalizedCore            = False
  , allowUnsafeConstructors       = False
  , ddumpTimings                  = False
  , modern                        = False
  , warnOnTermHoles               = False
  , refcore                       = False
  , refcoreText                   = False
  }

-- | A flag is either a config transformer or a request for --help/--version.
data Flag
  = FlagMod  (Config -> Config)
  | FlagHelp
  | FlagVersion

-- | The GetOpt option table.  Each entry lists all accepted long-option
-- names (aliases included) so that legacy pragmas keep working.
lhOptions :: [OptDescr Flag]
lhOptions =
  -- Verbosity
  [ opt [] ["minimal"]  (NoArg $ fm $ \c -> c { loggingVerbosity = Minimal })
      "Minimal logging verbosity (default)"
  , opt [] ["quiet"]    (NoArg $ fm $ \c -> c { loggingVerbosity = Quiet })
      "Silent logging verbosity"
  , opt [] ["normal"]   (NoArg $ fm $ \c -> c { loggingVerbosity = Normal })
      "Normal logging verbosity"
  , opt [] ["verbose"]  (NoArg $ fm $ \c -> c { loggingVerbosity = Loud })
      "Verbose logging"

  -- Checking mode
  , opt [] ["fullcheck"] (NoArg $ fm $ \c -> c { fullcheck = True })
      "Full Checking: check all binders (DEFAULT)"
  , opt [] ["diffcheck", "diff"] (NoArg $ fm $ \c -> c { diffcheck = True })
      "Incremental Checking: only check changed binders"
  , opt [] ["higherorder"] (NoArg $ fm $ \c -> c { higherorder = True })
      "Allow higher order binders into the logic"
  , opt [] ["higherorderqs"] (NoArg $ fm $ \c -> c { higherorderqs = True })
      "Allow higher order qualifiers to get automatically instantiated"
  , opt [] ["linear"] (NoArg $ fm $ \c -> c { linear = True })
      "Use uninterpreted integer multiplication and division"
  , opt [] ["string-theory", "stringtheory"] (NoArg $ fm $ \c -> c { stringTheory = True })
      "Interpretation of Strings by z3"
  , opt [] ["save-query", "save"] (NoArg $ fm $ \c -> c { saveQuery = True })
      "Save fixpoint query to file (slow)"
  , opt [] ["save-bfq-on-error"] (NoArg $ fm $ \c -> c { saveBfqOnError = True })
      "Save fixpoint query as .bfq only when verification fails"

  -- SMT
  , opt [] ["smt-timeout"] (ReqArg (fm . setSmtTimeout) "MSEC")
      "Timeout of smt queries in msec"
  , opt [] ["smtsolver"] (ReqArg (fm . setSmtSolverOpt) "SOLVER")
      "SMT solver to use: z3, z3mem, cvc4, cvc5, mathsat"
  , opt [] ["cores"] (ReqArg (fm . setCores) "N")
      (unlines
        [ "Number of cores to use (default 1)"
        , "Use the given number of cores to solve logical constraints (default: 1)."
        , "Warning: unpredictable performance."
        , "See https://github.com/ucsd-progsys/liquidhaskell/issues/2562"
        ]
      )
  , opt [] ["min-part-size"] (ReqArg (fm . setMinPartSize) "N")
      "Minimum partition size for multi-core solving"
  , opt [] ["max-part-size"] (ReqArg (fm . setMaxPartSize) "N")
      "Maximum partition size for multi-core solving"

  -- Checking options
  , opt [] ["check-var", "checks"] (ReqArg (fm . addCheckVar) "VAR")
      "Check a specific (top-level) binder (can be repeated)"
  , opt [] ["prune-unsorted", "pruneunsorted"] (NoArg $ fm $ \c -> c { pruneUnsorted = True })
      "Prune unsorted predicates"
  , opt [] ["no-termination-check", "no-termination", "notermination"]
      (NoArg $ fm $ \c -> c { notermination = True })
      "Disable Termination Check"
  , opt [] ["no-positivity-check"] (NoArg $ fm $ \c -> c { nopositivity = True })
      "Disable Data Type Positivity Check"
  , opt [] ["rankNTypes"] (NoArg $ fm $ \c -> c { rankNTypes = True })
      "Adds precise reasoning on presence of rankNTypes"
  , opt [] ["no-class-check", "noclasscheck"] (NoArg $ fm $ \c -> c { noclasscheck = True })
      "Disable Class Instance Check"
  , opt [] ["no-structural-termination", "nostruct"]
      (NoArg $ fm $ \c -> c { nostructuralterm = True })
      "Disable structural termination check"
  , opt [] ["bscope"] (NoArg $ fm $ \c -> c { bscope = True })
      "Scope of the outer binders on the inner refinements"
  , opt [] ["total-Haskell"] (NoArg $ fm $ \c -> c { totalHaskell = True })
      "Check for termination and totality; overrides no-termination flags"
  , opt [] ["no-warnings"] (NoArg $ fm $ \c -> c { nowarnings = True })
      "Don't display warnings, only show errors"
  , opt [] ["no-annotations"] (NoArg $ fm $ \c -> c { noannotations = True })
      "Don't create intermediate annotation files"
  , opt [] ["max-case-expand"] (ReqArg (fm . setCaseExpandDepth) "N")
      "Maximum depth at which to expand DEFAULT in case-of (default=2)"
  , opt [] ["no-true-types"] (NoArg $ fm $ \c -> c { notruetypes = True })
      "Disable Trueing Top Level Types"
  , opt [] ["no-totality"] (NoArg $ fm $ \c -> c { nototality = True })
      "Disable totality check"
  , opt [] ["totality"] (NoArg $ fm $ \c -> c { nototality = False })
      "Enable totality check (default)"
  , opt [] ["no-check-unknown"] (NoArg $ fm $ \c -> c { noCheckUnknown = True })
      "Don't complain about specifications for unexported and unused values"
  , opt [] ["max-params", "maxparams"] (ReqArg (fm . setMaxParams) "N")
      "Restrict qualifier mining to at most N parameters (default 2)"
  , opt [] ["short-names"] (NoArg $ fm $ \c -> c { shortNames = True })
      "Print shortened names, i.e. drop all module qualifiers"
  , opt [] ["short-errors"] (NoArg $ fm $ \c -> c { shortErrors = True })
      "Don't show long error messages, just line numbers"
  , opt [] ["adt"] (NoArg $ fm $ \c -> c { adtSpec = True })
      "Generate ADT representations in refinement logic"
  , opt [] ["expect-error-containing"] (ReqArg (fm . addExpectError) "MSG")
      "Expect an error containing MSG (can be repeated)"
  , opt [] ["expect-any-error"] (NoArg $ fm $ \c -> c { expectAnyError = True })
      "Expect an error, no matter which kind"
  , opt [] ["scrape-internals"] (NoArg $ fm $ \c -> c { scrapeInternals = True })
      "Scrape qualifiers from auto generated specifications"
  , opt [] ["elimStats"] (NoArg $ fm $ \c -> c { elimStats = True })
      "Print eliminate stats"
  , opt [] ["elimBound"] (ReqArg (fm . setElimBound) "N")
      "Maximum chain length for eliminating KVars"
  , opt [] ["noSlice"] (NoArg $ fm $ \c -> c { noslice = True })
      "Disable non-concrete KVar slicing"
  , opt [] ["no-lifted-imports"] (NoArg $ fm $ \c -> c { noLiftedImport = True })
      "Disable loading lifted specifications (for legacy libs)"
  , opt [] ["json"] (NoArg $ fm $ \c -> c { json = True })
      "Print results in JSON (for editor integration)"
  , opt [] ["counter-examples"] (NoArg $ fm $ \c -> c { counterExamples = True })
      "Attempt to generate counter-examples to type errors (experimental!)"
  , opt [] ["time-binds"] (NoArg $ fm $ \c -> c { timeBinds = True })
      "Solve each (top-level) asserted type signature separately & time solving"
  , opt [] ["untidy-core"] (NoArg $ fm $ \c -> c { untidyCore = True })
      "Print fully qualified identifier names in verbose mode"
  , opt [] ["eliminate"] (ReqArg (fm . setEliminate) "ELIM")
      (unlines
        [ "Use elimination for 'all', 'some' (default), 'none', 'horn', or 'existentials'"
        , "    all: use TRUE for cut-kvars"
        , "    some: use quals for cut-kvars"
        , "    none: use quals for all kvars"
        , "    horn: ??"
        , "    existentials: ??"
        ]
      )
  , opt [] ["no-pattern-inline"] (NoArg $ fm $ \c -> c { noPatternInline = True })
      "Don't inline special patterns (e.g. >>= and return) during constraint generation"
  , opt [] ["no-simplify-core"] (NoArg $ fm $ \c -> c { noSimplifyCore = True })
      "Don't simplify GHC core before constraint generation"

  -- PLE options
  , opt [] ["ple"] (NoArg $ fm $ \c -> c { proofLogicEval = True })
      "Enable Proof-by-Logical-Evaluation"
  , opt [] ["ple-with-undecided-guards"] (NoArg $ fm $ \c -> c { pleWithUndecidedGuards = True })
      "Unfold invocations with undecided guards in PLE"
  , opt [] ["interpreter"] (NoArg $ fm $ \c -> c { interpreter = True })
      "Use an interpreter to assist PLE in solving constraints"
  , opt [] ["ple-local"] (NoArg $ fm $ \c -> c { proofLogicEvalLocal = True })
      "Enable Proof-by-Logical-Evaluation locally, per function"
  , opt [] ["etabeta"] (NoArg $ fm $ \c -> c { etabeta = True })
      "Eta expand and beta reduce terms to aid PLE"
  , opt [] ["dependantcase"] (NoArg $ fm $ \c -> c { dependantCase = True })
      "Allow PLE to reason about dependent cases"
  , opt [] ["extensionality"] (NoArg $ fm $ \c -> c { extensionality = True })
      "Enable extensional interpretation of function equality"
  , opt [] ["fast"] (NoArg $ fm $ \c -> c { nopolyinfer = True })
      "No inference of polymorphic type application (imprecise but faster)"
  , opt [] ["reflection"] (NoArg $ fm $ \c -> c { reflection = True })
      "Enable reflection of Haskell functions and theorem proving"
  , opt [] ["compile-spec"] (NoArg $ fm $ \c -> c { compileSpec = True })
      "Only compile specifications (into .bspec file); skip verification"
  , opt [] ["typeclass"] (NoArg $ fm $ \c -> c { typeclass = True })
      "Enable Typeclass support"
  , opt [] ["aux-inline"] (NoArg $ fm $ \c -> c { auxInline = True })
      "Enable inlining of class methods"
  , opt [] ["rw-termination-check"] (NoArg $ fm $ \c -> c { rwTerminationCheck = True })
      ("Enable the rewrite divergence checker. Can speed up verification if rewriting\n" ++
       "terminates, but can also cause divergence."
      )
  , opt [] ["skip-module"] (NoArg $ fm $ \c -> c { skipModule = True })
      "Completely skip this module"
  , opt [] ["fuel"] (ReqArg (fm . setFuel) "N")
      "Maximum fuel (per-function unfoldings) for PLE"
  , opt [] ["environment-reduction"] (NoArg $ fm $ \c -> c { environmentReduction = True })
      "Perform environment reduction (disabled by default)"
  , opt [] ["no-environment-reduction"] (NoArg $ fm $ \c -> c { noEnvironmentReduction = True })
      "Don't perform environment reduction"
  , opt [] ["inline-anf-bindings"] (NoArg $ fm $ \c -> c { inlineANFBindings = True })
      ("Inline ANF bindings (sometimes improves performance and sometimes worsens it)\n" ++
       "Disabled by --no-environment-reduction"
      )
  , opt [] ["pandoc-html"] (NoArg $ fm $ \c -> c { pandocHtml = True })
      "Use pandoc to generate html"
  , opt [] ["exclude-automatic-assumptions-for"] (ReqArg (fm . addExcludeAssumptions) "PACKAGE")
      "Stop loading LHAssumptions modules for imports in these packages (repeat for multiple packages)"
  , opt [] ["dump-opaque-reflections"] (NoArg $ fm $ \c -> c { dumpOpaqueReflections = True })
      "Dump all generated opaque reflections"
  , opt [] ["dump-pre-normalized-core"] (NoArg $ fm $ \c -> c { dumpPreNormalizedCore = True })
      "Dump pre-normalized core (before a-normalization)"
  , opt [] ["dump-normalized-core"] (NoArg $ fm $ \c -> c { dumpNormalizedCore = True })
      "Dump a-normalized core"
  , opt [] ["allow-unsafe-constructors"] (NoArg $ fm $ \c -> c { allowUnsafeConstructors = True })
      "Allow refining constructors with unsafe refinements"
  , opt [] ["ddump-timings"] (NoArg $ fm $ \c -> c { ddumpTimings = True })
      "Dump time measures of the Liquid Haskell plugin"
  , opt [] ["refcore"] (NoArg $ fm $ \c -> c { refcore = True })
      "Extract RefCore Calculus declarations"
  , opt [] ["refcore-text"] (NoArg $ fm $ \c -> c { refcoreText = True })
      "Also write the human-readable .ilh text dump (debug)"
  , opt [] ["modern"] (NoArg $ fm $ \c -> c { modern = True })
      "Enable modern features (--reflection, --ple, --etabeta, --dependantcase)"
  , opt [] ["warn-on-term-holes"] (NoArg $ fm $ \c -> c { warnOnTermHoles = True })
      "Warn about holes in terms"

  -- Meta
  , opt "h" ["help"]    (NoArg FlagHelp)    "Show this help message"
  , opt "V" ["version"] (NoArg FlagVersion) "Show version information"
  ]
  where
    opt s l a h = Option s l a h
    fm          = FlagMod

-- | Helpers for option argument parsing.
setSmtTimeout :: String -> Config -> Config
setSmtTimeout s c = c { smtTimeout = Just (readInt "smt-timeout" s) }

setSmtSolverOpt :: String -> Config -> Config
setSmtSolverOpt s c = c { smtsolver = Just (parseSMTSolver s) }

setCores :: String -> Config -> Config
setCores s c = c { cores = Just (readInt "cores" s) }

setMinPartSize :: String -> Config -> Config
setMinPartSize s c = c { minPartSize = readInt "min-part-size" s }

setMaxPartSize :: String -> Config -> Config
setMaxPartSize s c = c { maxPartSize = readInt "max-part-size" s }

addCheckVar :: String -> Config -> Config
addCheckVar s c = c { checks = checks c ++ [s] }

setCaseExpandDepth :: String -> Config -> Config
setCaseExpandDepth s c = c { caseExpandDepth = readInt "max-case-expand" s }

setMaxParams :: String -> Config -> Config
setMaxParams s c = c { maxParams = readInt "max-params" s }

addExpectError :: String -> Config -> Config
addExpectError s c = c { expectErrorContaining = expectErrorContaining c ++ [s] }

setElimBound :: String -> Config -> Config
setElimBound s c = c { elimBound = Just (readInt "elimBound" s) }

setEliminate :: String -> Config -> Config
setEliminate s c = c { eliminate = parseEliminate s }

setFuel :: String -> Config -> Config
setFuel s c = c { fuel = Just (readInt "fuel" s) }

addExcludeAssumptions :: String -> Config -> Config
addExcludeAssumptions s c =
  c { excludeAutomaticAssumptionsFor = excludeAutomaticAssumptionsFor c ++ [s] }

readInt :: String -> String -> Int
readInt opt s = case reads s of
  [(n, "")] -> n
  _         -> error $ "Expected integer for --" ++ opt ++ ", got: " ++ show s

parseSMTSolver :: String -> FC.SMTSolver
parseSMTSolver s = case map toLower s of
  "z3"      -> FC.Z3
  "z3mem"   -> FC.Z3mem
  "z3 api"  -> FC.Z3mem
  "cvc4"    -> FC.Cvc4
  "cvc5"    -> FC.Cvc5
  "mathsat" -> FC.Mathsat
  _         -> error $ "Unknown SMT solver: " ++ show s
                     ++ ". Use one of: z3, z3mem, cvc4, cvc5, mathsat"

parseEliminate :: String -> FC.Eliminate
parseEliminate s = case map toLower s of
  "none"         -> FC.None
  "some"         -> FC.Some
  "all"          -> FC.All
  "horn"         -> FC.Horn
  "existentials" -> FC.Existentials
  _              -> error $ "Unknown eliminate value: " ++ show s
                          ++ ". Use one of: none, some, all, horn, existentials"

-- | Map LH's 'Verbosity' to liquid-fixpoint's 'Language.Fixpoint.Verbosity.Verbosity'
-- and set the global IORef so that whenLoud/whenNormal work throughout the solver.
setFxVerbosity :: Verbosity -> IO ()
setFxVerbosity Quiet   = FxV.setVerbosity FxV.Quiet
setFxVerbosity Minimal = FxV.setVerbosity FxV.Quiet
setFxVerbosity Normal  = FxV.setVerbosity FxV.Normal
setFxVerbosity Loud    = FxV.setVerbosity FxV.Loud

getOpts :: [String] -> IO Config
getOpts as = do
  cfg0 <- envCfg
  case getOpt Permute lhOptions as of
    (flags, _rest, []) -> do
      when (any isHelp    flags) $ putStr (formatHelp usageHeader lhOptions) >> error "LiquidHaskell:--help"
      when (any isVersion flags) $ putStrLn copyright >> error "LiquidHaskell:--version"
      let mods = [f | FlagMod f <- flags]
      let cfg1 = foldl (flip ($)) cfg0 mods
      let cfg2 = if json cfg1 then cfg1 { loggingVerbosity = Quiet } else cfg1
      setFxVerbosity (loggingVerbosity cfg2)
      withSmtSolver cfg2
    (_, _, optErrs) ->
      putStr (concat optErrs ++ formatHelp usageHeader lhOptions) >> exitFailure

usageHeader :: String
usageHeader = "Liquid Haskell Options:"

-- | Format the help text in a man-page style: each option's synopsis on its
-- own line, followed by the description indented on the next line.
--
-- Example output:
--
-- @
--   --ple
--
--           Enable Proof-by-Logical-Evaluation
--
--   --reflection
--
--           Enable reflection of Haskell functions and theorem proving
-- @
formatHelp :: String -> [OptDescr a] -> String
formatHelp hdr opts = unlines $ intercalate [""] $ [hdr] : map formatOne opts
  where
    formatOne (Option shorts longs argD helpTxt) =
      let indentedDesc = map ("        " ++) $ lines helpTxt
       in [ "  " ++ synopsis shorts longs argD
          , ""
          ] ++
          indentedDesc

    synopsis shorts longs argD =
      intercalate ", " $
           [ "-"  ++ [s]          | s <- shorts ]
        ++ [ "--" ++ l ++ argSuffix argD | l <- longs ]

    argSuffix (NoArg  _)    = ""
    argSuffix (ReqArg _ mv) = "=" ++ mv
    argSuffix (OptArg _ mv) = "[=" ++ mv ++ "]"


--------------------------------------------------------------------------------
withSmtSolver :: Config -> IO Config
--------------------------------------------------------------------------------
withSmtSolver cfg =
  case smtsolver cfg of
    Just smt -> do found <- findSmtSolver smt
                   case found of
                     Just _ -> return cfg
                     Nothing -> panic Nothing (missingSmtError smt)
    Nothing  -> do smts <- mapM findSmtSolver smtLookupOrder
                   case catMaybes smts of
                     (s:_) -> return (cfg {smtsolver = Just s})
                     _     -> panic Nothing noSmtError
  where
    smtLookupOrder = [FC.Z3, FC.Cvc5, FC.Cvc4, FC.Mathsat]
    noSmtError = "LiquidHaskell requires one of the following SMT solvers to be installed: " ++ intercalate ", " (show <$> smtLookupOrder) ++ "."
    missingSmtError smt = "Could not find SMT solver '" ++ show smt ++ "'. Is it on your PATH?"

findSmtSolver :: FC.SMTSolver -> IO (Maybe FC.SMTSolver)
findSmtSolver = \case
    FC.Z3mem -> return $ Just FC.Z3mem
    smt      -> maybe Nothing (const $ Just smt) <$> findExecutable (show smt)

-- | Parse the @LIQUIDHASKELL_OPTS@ environment variable (if set) to produce a
-- baseline 'Config'.  Unlike the old cmdargs-based @parsePragma@, this
-- implementation properly handles multiple space-separated options.
envCfg :: IO Config
envCfg = do
  so <- lookupEnv "LIQUIDHASKELL_OPTS"
  case so of
    Nothing -> return defConfig
    Just s  -> applyGetOpt defConfig (shellWords s)
  where
    applyGetOpt cfg toks =
      case getOpt Permute lhOptions toks of
        (flags, _, []) ->
          return $ foldl (flip ($)) cfg [f | FlagMod f <- flags]
        (_, _, optErrs) ->
          putStrLn (unlines optErrs) >> exitFailure

copyright :: String
copyright = concat $ concat
  [ ["LiquidHaskell "]
  , [$(simpleVersion Meta.version)]
  , [gitInfo]
  , ["\n\nCopyright 2013-19 Regents of the University of California. All Rights Reserved.\n"]
  ]

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
  , "] "
  ]


--------------------------------------------------------------------------------
-- | Updating options
--------------------------------------------------------------------------------
canonConfig :: Config -> Config
canonConfig cfg = cfg
  { diffcheck   = diffcheck cfg && not (fullcheck cfg)
  -- , eliminate   = if higherOrderFlag cfg then FC.All else eliminate cfg
  -- The "modern" flag is a sort of "super flag" which enables a bunch of
  -- features at once.
  , proofLogicEval = modern cfg || proofLogicEval cfg
  , etabeta        = modern cfg || etabeta cfg
  , dependantCase  = modern cfg || dependantCase cfg
  -- Technically those are patched in the `lookup` functions in `Congigs.hs` but
  -- it is better to be explicit here.
  , reflection     = modern cfg || reflection cfg
  }

--------------------------------------------------------------------------------
withPragmas :: MonadIO m => Config -> [Located String] -> (Config -> m a) -> m a
--------------------------------------------------------------------------------
withPragmas cfg ps action
  = do cfg' <- liftIO $ processPragmas cfg ps <&> canonConfig
       -- The global verbosity IORef (read by liquid-fixpoint) must be kept in
       -- sync whenever the verbosity may have changed.
       liftIO $ setFxVerbosity (loggingVerbosity cfg')
       res <- action cfg'
       liftIO $ setFxVerbosity (loggingVerbosity cfg) -- restore
       pure res

-- | Split a string into words like a shell would: unquoted whitespace
-- separates tokens, and single or double quoted substrings are kept as
-- one token (with the quotes stripped).  This allows option values that
-- contain spaces, e.g. @--expect-error-containing="Cannot ignore m"@.
shellWords :: String -> [String]
shellWords = filter (not . null) . go [] False False
  where
    -- @go acc dq sq cs@ processes the input string @cs@ character by character,
    -- accumulating the current token in 'acc', and keeping track of whether
    -- we're inside double quotes (dq) or single quotes (sq).
    go acc _  _  []     = [reverse acc | not (null acc)]
    go acc dq sq (c:cs)
      | c == '"'  && not sq = go acc (not dq) sq      cs
      | c == '\'' && not dq = go acc dq       (not sq) cs
      | isSpace c && not dq && not sq =
          if null acc then go [] False False cs
                      else reverse acc : go [] False False cs
      | otherwise            = go (c : acc) dq sq cs

-- | Apply a list of pragma strings (each is one option, e.g. @"--ple"@ or
-- @"--expect-error-containing=Mismatch"@) on top of an existing 'Config'.
processPragmas :: Config -> [Located String] -> IO Config
processPragmas cfg pragmas = foldM applyOne cfg pragmas
  where
    applyOne c loc =
      case getOpt Permute lhOptions [val loc] of
        (flags, _, []) -> do
          when (any isHelp flags) $
            putStr (formatHelp usageHeader lhOptions) >> error "LiquidHaskell:--help"
          when (any isVersion flags) $
            putStrLn copyright >> error "LiquidHaskell:--version"
          return $ foldl (flip ($)) c [f | FlagMod f <- flags]
        (_, _, optErrs)   ->
          putStrLn (unlines optErrs) >> exitFailure

isHelp :: Flag -> Bool
isHelp FlagHelp = True
isHelp _ = False

isVersion :: Flag -> Bool
isVersion FlagVersion = True
isVersion _ = False

-- | Parse a single pragma string against 'defConfig'.
-- Also used to parse the @LIQUIDHASKELL_OPTS@ environment variable.
parsePragma :: Located String -> IO Config
parsePragma = processPragmas defConfig . (:[])

-- | Write the annotations (i.e. the files in the \".liquid\" hidden folder) and
-- report the result of the checking using a supplied function, or using an
-- implicit JSON function, if @json@ flag is set.
reportResult :: MonadIO m
             => (OutputResult -> m ())
             -> Config
             -> [FilePath]
             -> Output Doc
             -> m ()
reportResult logResultFull cfg targets out = do
  annm <- {-# SCC "annotate" #-} liftIO $ annotate cfg targets out
  liftIO $ when (loggingVerbosity cfg >= Normal) $ F.donePhase F.Loud "annotate"
  if json cfg then
    liftIO $ reportResultJson annm
   else do
         let r = o_result out
         liftIO $ writeCheckVars $ o_vars out
         cr <- liftIO $ resultWithContext r
         let outputResult = resDocs tidy cr
         -- For now, always print the \"header\" with colours, irrespective to the logger
         -- passed as input.
         when (loggingVerbosity cfg >= Minimal) $
             liftIO $ printHeader (colorResult r) (orHeader outputResult)
         logResultFull outputResult
  where
    tidy :: F.Tidy
    tidy = if shortErrors cfg then F.Lossy else F.Full

    printHeader :: F.Moods -> Doc -> IO ()
    printHeader mood d = F.colorPhaseLn mood "" (render d)


reportResultJson :: ACSS.AnnMap -> IO ()
reportResultJson annm = do
  putStrLn "LIQUID"
  B.putStrLn . encode . annErrors $ annm

resultWithContext :: F.FixResult UserError -> IO (FixResult CError)
resultWithContext (F.Unsafe s es)  = F.Unsafe s    <$> errorsWithContext es
resultWithContext (F.Safe   stats) = return (F.Safe stats)
resultWithContext (F.Crash  es s)  = do
  let (userErrs, msgs) = unzip es
  errs' <- errorsWithContext userErrs
  return (F.Crash (zip errs' msgs) s)




instance Show (CtxError Doc) where
  show = showpp

writeCheckVars :: Symbolic a => Maybe [a] -> IO ()
writeCheckVars Nothing    = return ()
writeCheckVars (Just [])   = F.colorPhaseLn F.Loud "Checked Binders: None" ""
writeCheckVars (Just ns)   = F.colorPhaseLn F.Loud "Checked Binders:" ""
                          >> forM_ ns (putStrLn . symbolString . dropModuleNames . symbol)

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
  (pprint sSpan <> text ": error: ") $+$ nest 4 doc


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
    orHeader = text "LIQUID: ERROR:" <+> text s
  , orMessages = map (cErrToSpanned k . errToFCrash) xs
  }
resDocs k (F.Unsafe stats xs)   =
  OutputResult {
    orHeader   = text $ "LIQUID: UNSAFE (" <> show (Solver.numChck stats) <> " constraints checked)"
  , orMessages = map (cErrToSpanned k) (nub xs)
  }

-- | Renders a 'CError' into a 'Doc' and its associated 'SrcSpan'.
cErrToSpanned :: F.Tidy -> CError -> (GHC.SrcSpan, Doc)
cErrToSpanned k CtxError{ctErr} = (pos ctErr, pprintTidy k ctErr)

errToFCrash :: (CError, Maybe String) -> CError
errToFCrash (ce, Just msg) = ce { ctErr = ErrOther (pos (ctErr ce)) (fixMessageDoc msg) }
errToFCrash (ce, Nothing)  = ce { ctErr = tx $ ctErr ce}
  where
    tx (ErrSubType l m _ g t t') = ErrFCrash l m g t t'
    tx e                         = F.notracepp "errToFCrash?" e

fixMessageDoc :: String -> Doc
fixMessageDoc msg = vcat (text <$> lines msg)

{-
   TODO: Never used, do I need to exist?
reportUrl = text "Please submit a bug report at: https://github.com/ucsd-progsys/liquidhaskell" -}

addErrors :: FixResult a -> [a] -> FixResult a
addErrors r []                 = r
addErrors (Safe s) errors      = Unsafe s errors
addErrors (Unsafe s xs) errors = Unsafe s (xs ++ errors)
addErrors r  _                 = r

instance Fixpoint (F.FixResult CError) where
  toFix = vcat . map snd . orMessages . resDocs F.Full
