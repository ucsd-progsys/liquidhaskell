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


import Control.Monad
import Control.Monad.IO.Class
import Data.Maybe
import Data.Functor ((<&>))
import Data.Aeson (encode)
import qualified Data.ByteString.Lazy.Char8 as B
import Development.GitRev (gitCommitCount)
import qualified Paths_liquidhaskell_boot as Meta
import System.Directory
import System.Exit
import System.Environment
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Implicit     hiding (Verbosity(..))
import System.Console.CmdArgs.Text
import GitHash

import Data.List                           (nub, intercalate)


import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Misc as F
import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types             hiding (panic, Error, Result, saveQuery)
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Solver.Stats as Solver
import Language.Haskell.Liquid.UX.Annotate
import Language.Haskell.Liquid.UX.Config
import Language.Haskell.Liquid.UX.SimpleVersion (simpleVersion)
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Types.Errors hiding (typ)
import Language.Haskell.Liquid.Types.PrettyPrint ()
import Language.Haskell.Liquid.Types.Types
import qualified Language.Haskell.Liquid.UX.ACSS as ACSS

import qualified Liquid.GHC.API as GHC
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
config = cmdArgsMode defConfig

defConfig :: Config
defConfig = Config {
  loggingVerbosity
    = enum [ Minimal      &= name "minimal" &= help "Minimal logging verbosity"
           , Quiet        &= name "quiet"   &= help "Silent logging verbosity"
           , Normal       &= name "normal"  &= help "Normal logging verbosity"
           , Loud         &= name "verbose" &= help "Verbose logging"
           ]
           
 , saveBfqOnly 
      = def
           &= help "Only save .bfq files when verification fails"
            &= name "save-bfq-only"        

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
    = False &= help "Disable prunning unsorted Predicates"
          &= name "prune-unsorted"

 , notermination
    = False
          &= help "Disable Termination Check"
          &= name "no-termination-check"

 , nopositivity
    = False
          &= help "Disable Data Type Positivity Check"
          &= name "no-positivity-check"

 , rankNTypes
    = False &= help "Adds precise reasoning on presence of rankNTypes"
          &= name "rankNTypes"

 , noclasscheck
    = False
          &= help "Disable Class Instance Check"
          &= name "no-class-check"

 , nostructuralterm
    = def &= name "no-structural-termination"
          &= help "Disable structural termination check"

 , bscope
    = False &= help "scope of the outer binders on the inner refinements"
          &= name "bscope"

 , totalHaskell
    = False &= help "Check for termination and totality; overrides no-termination flags"
          &= name "total-Haskell"

 , nowarnings
    = False &= help "Don't display warnings, only show errors"
          &= name "no-warnings"

 , noannotations
    = False &= help "Don't create intermediate annotation files"
          &= name "no-annotations"

 , checkDerived
    = False &= help "Check GHC generated binders (e.g. Read, Show instances)"
          &= name "check-derived"

 , caseExpandDepth
    = 2   &= help "Maximum depth at which to expand DEFAULT in case-of (default=2)"
          &= name "max-case-expand"

 , notruetypes
    = False &= help "Disable Trueing Top Level Types"
          &= name "no-true-types"

 , nototality
    = False &= help "Disable totality check"
          &= name "no-totality"

 , cores
    = Just 1 &= help "Use the given number of cores to solve logical constraints (default: 1). Warning: unpredictable performance. See https://github.com/ucsd-progsys/liquidhaskell/issues/2562"

 , minPartSize
    = FC.defaultMinPartSize
    &= help "If solving on multiple cores, ensure that partitions are of at least m size"

 , maxPartSize
    = FC.defaultMaxPartSize
    &= help ("If solving on multiple cores, once there are as many partitions " ++
             "as there are cores, don't merge partitions if they will exceed this " ++
             "size. Overrides the minpartsize option.")

 , smtsolver
    = Nothing &= help "Name of SMT-Solver"

 , noCheckUnknown
    = def &= explicit
          &= name "no-check-unknown"
          &= help "Don't complain about specifications for unexported and unused values "

 , maxParams
    = defaultMaxParams &= help "Restrict qualifier mining to those taking at most `m' parameters (2 by default)"

 , shortNames
    = False &= name "short-names"
          &= help "Print shortened names, i.e. drop all module qualifiers."

 , shortErrors
    = False &= name "short-errors"
          &= help "Don't show long error messages, just line numbers."

 , exactDC
    = False &= help "Exact Type for Data Constructors"
          &= name "exact-data-cons"

 , noADT
    = False &= help "Do not generate ADT representations in refinement logic"
          &= name "no-adt"
          
 , expectErrorContaining
    = [] &= help "Expect an error which containing the provided string from verification (can be provided more than once)"
          &= name "expect-error-containing"

 , expectAnyError
    = False &= help "Expect an error, no matter which kind or what it contains"
          &= name "expect-any-error"

 , scrapeInternals
    = False &= help "Scrape qualifiers from auto generated specifications"
            &= name "scrape-internals"
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
    = False
        &= help "Enable Proof-by-Logical-Evaluation"
        &= name "ple"

  , pleWithUndecidedGuards
    = False
        &= help "Unfold invocations with undecided guards in PLE"
        &= name "ple-with-undecided-guards"
        &= explicit

  , interpreter
    = False
        &= help "Use an interpreter to assist PLE in solving constraints"
        &= name "interpreter"

  , proofLogicEvalLocal
    = False
        &= help "Enable Proof-by-Logical-Evaluation locally, per function"
        &= name "ple-local"

  , etabeta
    = False
        &= help "Eta expand and beta reduce terms to aid PLE"
        &= name "etabeta"

  , dependantCase
    = False
        &= help "Allow PLE to reason about dependent cases"
        &= name "dependant-case"

  , extensionality
    = False
        &= help "Enable extensional interpretation of function equality"
        &= name "extensionality"

  , nopolyinfer
    = False
        &= help "No inference of polymorphic type application. Gives imprecision, but speedup."
        &= name "fast"

  , reflection
    = False
        &= help "Enable reflection of Haskell functions and theorem proving"
        &= name "reflection"

  , compileSpec
    = False
        &= name "compile-spec"
        &= help "Only compile specifications (into .bspec file); skip verification"

  , typeclass
    = False
        &= help "Enable Typeclass"
        &= name "typeclass"
  , auxInline
    = False
        &= help "Enable inlining of class methods"
        &= name "aux-inline"
  ,
    rwTerminationCheck
    = False
        &= name "rw-termination-check"
        &= help (   "Enable the rewrite divergence checker. "
                 ++ "Can speed up verification if rewriting terminates, but can also cause divergence."
                )
  ,
    skipModule
    = False
        &= name "skip-module"
        &= help "Completely skip this module, don't even compile any specifications in it."

  , fuel
    = Nothing
        &= help "Maximum fuel (per-function unfoldings) for PLE"

  , environmentReduction
    = False
        &= explicit
        &= name "environment-reduction"
        &= help "perform environment reduction (disabled by default)"
  , noEnvironmentReduction
    = False
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
  , excludeAutomaticAssumptionsFor
    = []
      &= explicit
      &= name "exclude-automatic-assumptions-for"
      &= help "Stop loading LHAssumptions modules for imports in these packages."
      &= typ "PACKAGE"
  , dumpOpaqueReflections
    = False &= help "Dump all generated opaque reflections"
          &= name "dump-opaque-reflections"
          &= explicit
  , dumpPreNormalizedCore
    = False &= help "Dump pre-normalized core (before a-normalization)"
          &= name "dump-pre-normalized-core"
          &= explicit
  , dumpNormalizedCore
    = False &= help "Dump a-normalized core"
          &= name "dump-normalized-core"
          &= explicit
  , allowUnsafeConstructors
    = False &= help "Allow refining constructors with unsafe refinements"
          &= name "allow-unsafe-constructors"
          &= explicit
  , ddumpTimings
    = False &= help "Dump time measures of the Liquid Haskell plugin"
          &= name "ddump-timings"
          &= explicit
  } &= program "liquidhaskell"
    &= help    "Refinement Types for Haskell"
    &= summary copyright
    &= details [ "LiquidHaskell is a Refinement Type based verifier for Haskell" ]

getOpts :: [String] -> IO Config
getOpts as = do
  cfg0   <- envCfg
  cfg1   <- cmdArgsRun'
              config { modeValue = (modeValue config)
                                      { cmdArgsValue   = cfg0 }
                     }
                     as
  let cfg2 = if json cfg1 then cfg1 {loggingVerbosity = Quiet} else cfg1
  setVerbosity (cmdargsVerbosity $ loggingVerbosity cfg2)
  withSmtSolver cfg2

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


--------------------------------------------------------------------------------
-- | Updating options
--------------------------------------------------------------------------------
canonConfig :: Config -> Config
canonConfig cfg = cfg
  { diffcheck   = diffcheck cfg && not (fullcheck cfg)
  -- , eliminate   = if higherOrderFlag cfg then FC.All else eliminate cfg
  }

--------------------------------------------------------------------------------
withPragmas :: MonadIO m => Config -> [Located String] -> (Config -> m a) -> m a
--------------------------------------------------------------------------------
withPragmas cfg ps action
  = do cfg' <- liftIO $ processPragmas cfg ps <&> canonConfig
       -- As the verbosity is set /globally/ via the cmdargs lib, re-set it.
       liftIO $ setVerbosity (cmdargsVerbosity $ loggingVerbosity cfg')
       res <- action cfg'
       liftIO $ setVerbosity (cmdargsVerbosity $ loggingVerbosity cfg) -- restore the original verbosity.
       pure res

processPragmas :: Config -> [Located String] -> IO Config
processPragmas c pragmas =
    processValueIO
      config { modeValue = (modeValue config) { cmdArgsValue = c } }
      (val <$> pragmas)
    >>=
      cmdArgsApply

-- | Note that this function doesn't process list arguments properly, like
-- 'expectErrorContaining'
-- TODO: This is only used to parse the contents of the env var LIQUIDHASKELL_OPTS
-- so it should be able to parse multiple arguments instead. See issue #1990.
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
