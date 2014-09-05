{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# OPTIONS_GHC -fno-cse #-}

-- | This module contains all the code needed to output the result which
--   is either: `SAFE` or `WARNING` with some reasonable error message when
--   something goes wrong. All forms of errors/exceptions should go through
--   here. The idea should be to report the error, the source position that
--   causes it, generate a suitable .json file and then exit.


module Language.Haskell.Liquid.CmdLine (
   -- * Get Command Line Configuration
     getOpts, mkOpts

   -- * Update Configuration With Pragma
   , withPragmas

   -- * Exit Function
   , exitWithResult

   -- * Diff check mode
   , diffcheck
) where

import           Control.Applicative                 ((<$>))
import           Control.DeepSeq
import           Control.Monad

import qualified Data.HashMap.Strict                 as M
import           Data.List                           (foldl', nub)
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text                           as T
import qualified Data.Text.IO                        as TIO

import           System.Console.CmdArgs              hiding (Loud)
import           System.Console.CmdArgs.Verbosity    (whenLoud)
import           System.Directory                    (doesDirectoryExist, canonicalizePath, getCurrentDirectory)
import           System.Environment                  (lookupEnv, withArgs)
import           System.FilePath                     (dropFileName, isAbsolute,
                                                      takeDirectory, (</>))
import           System.Posix.Files                  (getFileStatus,
                                                      isDirectory)

import           Language.Fixpoint.Config            hiding (Config, config,
                                                      real)
import           Language.Fixpoint.Files
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Names             (dropModuleNames)
import           Language.Fixpoint.Types             hiding (config)
import           Language.Haskell.Liquid.Annotate
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.PrettyPrint
import           Language.Haskell.Liquid.Types       hiding (config, name, typ)

import           Name
import           SrcLoc                              (SrcSpan)
import           Text.Parsec.Pos                     (newPos)
import           Text.PrettyPrint.HughesPJ


---------------------------------------------------------------------------------
-- Parsing Command Line----------------------------------------------------------
---------------------------------------------------------------------------------

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

 , binders
    = def &= help "Check a specific set of binders"

 , noPrune
    = def &= help "Disable prunning unsorted Predicates"
          &= name "no-prune-unsorted"

 , notermination
    = def &= help "Disable Termination Check"
          &= name "no-termination-check"

 , trustinternals
    = def &= help "Trust all ghc auto generated code"
          &= name "trust-interals"

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

 , smtsolver
    = def &= help "Name of SMT-Solver"

 , noCheckUnknown
    = def &= explicit
          &= name "no-check-unknown"
          &= help "Don't complain about specifications for unexported and unused values "

 , maxParams
    = 2   &= help "Restrict qualifier mining to those taking at most `m' parameters (2 by default)"

 , shortNames
    = def &= name "short-names"
          &= help "Print shortened names, i.e. drop all module qualifiers."

 , shortErrors
    = def &= name "short-errors"
          &= help "Don't show long error messages, just line numbers."

 , ghcOptions
    = def &= name "ghc-option"
          &= typ "OPTION"
          &= help "Pass this option to GHC"

 , cFiles
    = def &= name "c-files"
          &= typ "OPTION"
          &= help "Tell GHC to compile and link against these files"

 -- , verbose
 --    = def &= help "Generate Verbose Output"
 --          &= name "verbose-output"

 } &= verbosity
   &= program "liquid"
   &= help    "Refinement Types for Haskell"
   &= summary copyright
   &= details [ "LiquidHaskell is a Refinement Type based verifier for Haskell"
              , ""
              , "To check a Haskell file foo.hs, type:"
              , "  liquid foo.hs "
              ]

getOpts :: IO Config
getOpts = do cfg0    <- envCfg
             cfg1    <- mkOpts =<< cmdArgsRun config
             pwd     <- getCurrentDirectory
             cfg     <- canonicalizePaths (fixCfg $ mconcat [cfg0, cfg1]) pwd
             whenNormal $ putStrLn copyright
             return cfg

-- | Attempt to canonicalize all `FilePath's in the `Config' so we don't have
--   to worry about relative paths.
canonicalizePaths :: Config -> FilePath -> IO Config
canonicalizePaths cfg tgt
  = do st  <- getFileStatus tgt
       tgt <- canonicalizePath tgt
       dir <- doesDirectoryExist tgt
       let canonicalize f
             | isAbsolute f   = return f
             | isDirectory st = canonicalizePath (tgt </> f)
             | otherwise      = canonicalizePath (takeDirectory tgt </> f)
       is <- mapM canonicalize $ idirs cfg
       cs <- mapM canonicalize $ cFiles cfg
       return $ cfg { idirs = is, cFiles = cs }


fixCfg cfg = cfg { diffcheck = diffcheck cfg && not (fullcheck cfg) }

envCfg = do so <- lookupEnv "LIQUIDHASKELL_OPTS"
            case so of
              Nothing -> return mempty
              Just s  -> parsePragma $ envLoc s
         where
            envLoc  = Loc (newPos "ENVIRONMENT" 0 0)

copyright = "LiquidHaskell © Copyright 2009-14 Regents of the University of California. All Rights Reserved.\n"

mkOpts :: Config -> IO Config
mkOpts cfg
  = do files' <- sortNub . concat <$> mapM getHsTargets (files cfg)
       -- idirs' <- if null (idirs cfg) then single <$> getIncludeDir else return (idirs cfg)
       id0 <- getIncludeDir
       return  $ cfg { files = files' }
                     { idirs = (dropFileName <$> files') ++ [id0] ++ idirs cfg }
                              -- tests fail if you flip order of idirs'

---------------------------------------------------------------------------------------
-- | Updating options
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
withPragmas :: Config -> FilePath -> [Located String] -> IO Config
---------------------------------------------------------------------------------------
withPragmas cfg fp ps
  = foldM withPragma cfg ps >>= flip canonicalizePaths fp

withPragma :: Config -> Located String -> IO Config
withPragma c s = (c `mappend`) <$> parsePragma s

parsePragma   :: Located String -> IO Config
parsePragma s = withArgs [val s] $ cmdArgsRun config

---------------------------------------------------------------------------------------
-- | Monoid instances for updating options
---------------------------------------------------------------------------------------


instance Monoid Config where
  mempty        = Config def def def def def def def def def def def def def def 2 def def def def def
  mappend c1 c2 = Config { files          = sortNub $ files c1   ++     files          c2
                         , idirs          = sortNub $ idirs c1   ++     idirs          c2
                         , fullcheck      = fullcheck c1         ||     fullcheck      c2
                         , real           = real      c1         ||     real           c2
                         , diffcheck      = diffcheck c1         ||     diffcheck      c2
                         , binders        = sortNub $ binders c1 ++     binders        c2
                         , noCheckUnknown = noCheckUnknown c1    ||     noCheckUnknown c2
                         , notermination  = notermination  c1    ||     notermination  c2
                         , trustinternals = trustinternals c1    ||     trustinternals c2
                         , nocaseexpand   = nocaseexpand   c1    ||     nocaseexpand   c2
                         , strata         = strata         c1    ||     strata         c2
                         , notruetypes    = notruetypes    c1    ||     notruetypes    c2
                         , totality       = totality       c1    ||     totality       c2
                         , noPrune        = noPrune        c1    ||     noPrune        c2
                         , maxParams      = maxParams      c1   `max`   maxParams      c2
                         , smtsolver      = smtsolver c1      `mappend` smtsolver      c2
                         , shortNames     = shortNames c1        ||     shortNames     c2
                         , shortErrors    = shortErrors c1       ||     shortErrors    c2
                         , ghcOptions     = ghcOptions c1        ++     ghcOptions     c2
                         , cFiles         = cFiles c1            ++     cFiles         c2
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
  = do let r  = o_result out
       let rs = showFix r
       {-# SCC "annotate" #-} annotate cfg target out
       donePhase Loud "annotate"
       writeCheckVars $ o_vars  out
       writeWarns     $ o_warns out
       writeResult cfg (colorResult r) r
       writeFile   (extFileName Result target) rs
       return $ out { o_result = if null (o_warns out) then r else Unsafe [] }

writeWarns []            = return ()
writeWarns ws            = colorPhaseLn Angry "Warnings:" "" >> putStrLn (unlines $ nub ws)

writeCheckVars Nothing   = return ()
writeCheckVars (Just []) = colorPhaseLn Loud "Checked Binders: None" ""
writeCheckVars (Just ns) = colorPhaseLn Loud "Checked Binders:" "" >> forM_ ns (putStrLn . symbolString . dropModuleNames . symbol)

writeResult cfg c        = mapM_ (writeDoc c) . zip [0..] . resDocs tidy
  where
    tidy                 = if shortErrors cfg then Lossy else Full
    writeDoc c (i, d)    = writeBlock c i $ lines $ render d
    writeBlock c _ []    = return ()
    writeBlock c 0 ss    = forM_ ss (colorPhaseLn c "")
    writeBlock c _ ss    = forM_ ("\n" : ss) putStrLn

resDocs _ Safe             = [text "SAFE"]
resDocs k (Crash xs s)     = text ("CRASH: " ++ s) : pprManyOrdered k "" xs
resDocs k (Unsafe xs)      = text "UNSAFE" : pprManyOrdered k "" (nub xs)
resDocs _ (UnknownError d) = [text $ "PANIC: Unexpected Error: " ++ d, reportUrl]

reportUrl              = text "Please submit a bug report at: https://github.com/ucsd-progsys/liquidhaskell"


instance Fixpoint (FixResult Error) where
  toFix = vcat . resDocs Full

