{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# OPTIONS_GHC -fno-cse #-}

{-@ LIQUID "--cabaldir" @-}
{-@ LIQUID "--diff"     @-}

-- | This module contains all the code needed to output the result which
--   is either: `SAFE` or `WARNING` with some reasonable error message when
--   something goes wrong. All forms of errors/exceptions should go through
--   here. The idea should be to report the error, the source position that
--   causes it, generate a suitable .json file and then exit.


module Language.Haskell.Liquid.UX.CmdLine (
   -- * Get Command Line Configuration
     getOpts, mkOpts

   -- * Update Configuration With Pragma
   , withPragmas
   , withCabal

   -- * Exit Function
   , exitWithResult

   -- * Diff check mode
   , diffcheck

) where

import Control.Monad
import Data.Maybe
import System.Directory
import System.Exit
import System.Environment

import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Implicit     hiding (Loud)
import System.Console.CmdArgs.Text

import Data.List                           (nub)
import Data.Monoid

import System.FilePath                     (dropFileName, isAbsolute,
                                            takeDirectory, (</>))

import Language.Fixpoint.Types.Config      hiding (Config, real, extSolver,
                                              getOpts, cores, minPartSize,
                                              maxPartSize, newcheck, eliminate)
import Language.Fixpoint.Utils.Files
import Language.Fixpoint.Misc
import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types             hiding (Error, Result)
import Language.Haskell.Liquid.UX.Annotate
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.UX.PrettyPrint
import Language.Haskell.Liquid.Types       hiding (config, name, typ)
import Language.Haskell.Liquid.UX.Errors
import Language.Haskell.Liquid.UX.Cabal

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

 , real
    = def
          &= help "Supports real number arithmetic"

 , exactDC
    = def &= help "Exact Type for Data Constructors"
          &= name "exact-data-cons"

 , extSolver
    = def &= help "Use external (OCaml) fixpoint constraint solver"

 , binders
    = def &= help "Check a specific set of binders"

 , noPrune
    = def &= help "Disable prunning unsorted Predicates"
          &= name "no-prune-unsorted"

 , notermination
    = def &= help "Disable Termination Check"
          &= name "no-termination-check"

 , autoproofs
    = def &= help "Automatically construct proofs from axioms"
          &= name "auto-proofs"

 , nowarnings
    = def &= help "Don't display warnings, only show errors"
          &= name "no-warnings"

 , trustinternals
    = def &= help "Trust all ghc auto generated code"
          &= name "trust-internals"

 , nocaseexpand
    = def &= help "Disable Termination Check"
          &= name "no-case-expand"
 , strata
    = def &= help "Enable Strata Analysis"

 , notruetypes
    = def &= help "Disable Trueing Top Level Types"
          &= name "no-true-types"

 , totality
    = def &= help "Check totality"

 , cores
    = def &= help "Use m cores to solve logical constraints"

 , minPartSize
    = defaultMinPartSize &= help "If solving on multiple cores, ensure that partitions are of at least m size"

 , maxPartSize
    = defaultMaxPartSize &= help ("If solving on multiple cores, once there are as many partitions " ++
                                  "as there are cores, don't merge partitions if they will exceed this " ++
                                  "size. Overrides the minpartsize option.")

 , smtsolver
    = def &= help "Name of SMT-Solver"

 , newcheck
    = True &= help "New fixpoint check"

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

 , eliminate
    = def &= name "eliminate"
          &= help "Use experimental 'eliminate' feature"

 , port
     = defaultPort
          &= name "port"
          &= help "Port at which lhi should listen"

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
                         config { modeValue = (modeValue config) { cmdArgsValue = cfg0 } }
                         as
  cfg    <- fixConfig cfg1
  whenNormal $ putStrLn copyright
  withSmtSolver cfg


cmdArgsRun' :: Mode (CmdArgs a) -> [String] -> IO a
cmdArgsRun' md as
  = case parseResult of
      Left e  -> putStrLn (helpMsg e) >> exitFailure
      Right a -> cmdArgsApply a
    where
      helpMsg e = showText defaultWrap $ helpText [e] HelpFormatDefault md
      parseResult = process md as -- <$> getArgs

--------------------------------------------------------------------------------
withSmtSolver :: Config -> IO Config
--------------------------------------------------------------------------------
withSmtSolver cfg =
  case smtsolver cfg of
    Just _  -> return cfg
    Nothing -> do smts <- mapM findSmtSolver [Z3, Cvc4, Mathsat]
                  case catMaybes smts of
                    (s:_) -> return (cfg {smtsolver = Just s})
                    _     -> exitWithPanic noSmtError
  where
    noSmtError = "LiquidHaskell requires an SMT Solver, i.e. z3, cvc4, or mathsat to be installed."

findSmtSolver :: SMTSolver -> IO (Maybe SMTSolver)
findSmtSolver smt = maybe Nothing (const $ Just smt) <$> findExecutable (show smt)

fixConfig :: Config -> IO Config
fixConfig cfg = do
  pwd <- getCurrentDirectory
  cfg <- canonicalizePaths pwd cfg
  -- cfg <- withCabal cfg
  return $ fixDiffCheck cfg

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

fixDiffCheck :: Config -> Config
fixDiffCheck cfg = cfg { diffcheck = diffcheck cfg && not (fullcheck cfg) }

envCfg = do so <- lookupEnv "LIQUIDHASKELL_OPTS"
            case so of
              Nothing -> return defConfig
              Just s  -> parsePragma $ envLoc s
         where
            envLoc  = Loc l l
            l       = newPos "ENVIRONMENT" 0 0

copyright = "LiquidHaskell Copyright 2009-15 Regents of the University of California. All Rights Reserved.\n"

mkOpts :: Config -> IO Config
mkOpts cfg
  = do let files' = sortNub $ files cfg
       id0 <- getIncludeDir
       return  $ cfg { files = files' }
                     { idirs = (dropFileName <$> files') ++ [id0 </> gHC_VERSION, id0] ++ idirs cfg }
                              -- tests fail if you flip order of idirs'

---------------------------------------------------------------------------------------
-- | Updating options
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
withPragmas :: Config -> FilePath -> [Located String] -> IO Config
---------------------------------------------------------------------------------------
withPragmas cfg fp ps = foldM withPragma cfg ps >>= canonicalizePaths fp

withPragma :: Config -> Located String -> IO Config
withPragma c s = withArgs [val s] $ cmdArgsRun
          config { modeValue = (modeValue config) { cmdArgsValue = c } }
   --(c `mappend`) <$> parsePragma s

parsePragma   :: Located String -> IO Config
parsePragma = withPragma defConfig
   --withArgs [val s] $ cmdArgsRun config

---------------------------------------------------------------------------------------
withCabal :: Config -> IO Config
---------------------------------------------------------------------------------------
withCabal cfg
  | cabalDir cfg = withCabal' cfg
  | otherwise    = return cfg

withCabal' cfg = do
  whenLoud $ putStrLn $ "addCabalDirs: " ++ tgt
  io <- cabalInfo tgt
  case io of
    Just i  -> return $ fixCabalDirs' cfg i
    Nothing -> exitWithPanic "Cannot find .cabal information!"
  where
    tgt = case files cfg of
            f:_ -> f
            _   -> exitWithPanic "Please provide a target file to verify."


fixCabalDirs' :: Config -> Info -> Config
fixCabalDirs' cfg i = cfg { idirs      = nub $ idirs cfg ++ sourceDirs i ++ buildDirs i }
                          { ghcOptions = ghcOptions cfg ++ dbOpts ++ pkOpts
                                      ++ ["-optP-include", "-optP" ++ macroPath i]}
   where
     dbOpts         = ["-package-db " ++ db | db <- packageDbs  i]
     pkOpts         = ["-package "    ++ n  | n  <- packageDeps i] -- SPEED HIT for smaller benchmarks

defConfig :: Config
defConfig = Config { files          = def
                   , idirs          = def
                   , newcheck       = True
                   , fullcheck      = def
                   , real           = def
                   , diffcheck      = def
                   , extSolver      = def
                   , binders        = def
                   , noCheckUnknown = def
                   , notermination  = def
                   , autoproofs     = def
                   , nowarnings     = def
                   , trustinternals = def
                   , nocaseexpand   = def
                   , strata         = def
                   , notruetypes    = def
                   , totality       = def
                   , noPrune        = def
                   , exactDC        = def
                   , cores          = def
                   , minPartSize    = defaultMinPartSize
                   , maxPartSize    = defaultMaxPartSize
                   , maxParams      = defaultMaxParams
                   , smtsolver      = def
                   , shortNames     = def
                   , shortErrors    = def
                   , cabalDir       = def
                   , ghcOptions     = def
                   , cFiles         = def
                   , eliminate      = def
                   , port           = defaultPort
                   }

instance Monoid SMTSolver where
  mempty        = def
  mappend s1 s2
    | s1 == s2  = s1
    | s2 == def = s1
    | otherwise = s2


------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
exitWithResult :: Config -> FilePath -> Output Doc -> IO (Output Doc)
------------------------------------------------------------------------
exitWithResult cfg target out
  = do {-# SCC "annotate" #-} annotate cfg target out
       donePhase Loud "annotate"
       writeCheckVars $ o_vars  out
       writeResult cfg (colorResult r) r
       writeFile   (extFileName Result target) (showFix r)
       return $ out { o_result = r }
    where
       r         = o_result out `addErrors` o_errors out


writeCheckVars Nothing     = return ()
writeCheckVars (Just [])   = colorPhaseLn Loud "Checked Binders: None" ""
writeCheckVars (Just ns)   = colorPhaseLn Loud "Checked Binders:" "" >> forM_ ns (putStrLn . symbolString . dropModuleNames . symbol)

writeResult cfg c          = mapM_ (writeDoc c) . zip [0..] . resDocs tidy
  where
    tidy                   = if shortErrors cfg then Lossy else Full
    writeDoc c (i, d)      = writeBlock c i $ lines $ render d
    writeBlock _ _ []      = return ()
    writeBlock c 0 ss      = forM_ ss (colorPhaseLn c "")
    writeBlock _  _ ss     = forM_ ("\n" : ss) putStrLn

resDocs _ Safe             = [text "RESULT: SAFE"]
resDocs k (Crash xs s)     = text ("RESULT: ERROR") : text s : pprManyOrdered k "" (errToFCrash <$> xs)
resDocs k (Unsafe xs)      = text "RESULT: UNSAFE" : pprManyOrdered k "" (nub xs)
-- resDocs _ (UnknownError d) = [text $ "RESULT: PANIC: Unexpected Error: " ++ d, reportUrl]

{-
   TODO: Never used, do I need to exist?
reportUrl              = text "Please submit a bug report at: https://github.com/ucsd-progsys/liquidhaskell" -}


addErrors r []             = r
addErrors Safe errs        = Unsafe errs
addErrors (Unsafe xs) errs = Unsafe (xs ++ errs)
addErrors r  _             = r

instance Fixpoint (FixResult Error) where
  toFix = vcat . resDocs Full
