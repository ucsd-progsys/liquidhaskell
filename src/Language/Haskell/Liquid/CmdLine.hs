{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}

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

   -- * Extra Outputs
   , Output (..)
) where

import Control.DeepSeq
import Control.Monad
import Control.Applicative                      ((<$>))

import           Data.List                                (foldl', nub)
import           Data.Maybe
import           Data.Monoid
import qualified Data.HashMap.Strict as M

import           System.FilePath                          (dropFileName)
import           System.Environment                       (withArgs)
import           System.Console.CmdArgs  hiding           (Loud)                
import           System.Console.CmdArgs.Verbosity         (whenLoud)            

import Language.Fixpoint.Misc
import Language.Fixpoint.Files
import Language.Fixpoint.Names                  (dropModuleNames)
import Language.Fixpoint.Types hiding           (config)
import Language.Fixpoint.Config hiding          (config, Config)
import Language.Haskell.Liquid.Annotate
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.PrettyPrint
import Language.Haskell.Liquid.Types hiding     (config, typ, name)

import Name
import SrcLoc                                   (SrcSpan)
import Text.PrettyPrint.HughesPJ    


---------------------------------------------------------------------------------
-- Parsing Command Line----------------------------------------------------------
---------------------------------------------------------------------------------

config = Config { 
   files    
    = def &= typ "TARGET" 
          &= args 
          &= typFile 
 
 , idirs 
    = def &= typDir 
          &= help "Paths to Spec Include Directory " 
   
 , diffcheck 
    = def 
          &= help "Incremental Checking: only check changed binders" 

 , binders
    = def &= help "Check a specific set of binders"

 , noPrune 
    = def &= help "Disable prunning unsorted Predicates"
          &= name "no-prune-unsorted"

 , notermination 
    = def &= help "Disable Termination Check"
          &= name "no-termination-check"

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

 , ghcOptions
    = def &= name "ghc-option"
          &= typ "OPTION"
          &= help "Pass this option to GHC"
 
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
getOpts = do md <- cmdArgs config 
             putStrLn copyright
             whenLoud $ putStrLn $ "liquid " ++ show md ++ "\n"
             mkOpts md

copyright = "LiquidHaskell © Copyright 2009-13 Regents of the University of California. All Rights Reserved.\n"

mkOpts :: Config -> IO Config
mkOpts md  
  = do files' <- sortNub . concat <$> mapM getHsTargets (files md) 
       -- idirs' <- if null (idirs md) then single <$> getIncludeDir else return (idirs md)
       id0 <- getIncludeDir 
       return  $ md { files = files' } 
                    { idirs = (dropFileName <$> files') ++ [id0] ++ idirs md }
                              -- tests fail if you flip order of idirs'

---------------------------------------------------------------------------------------
-- | Updating options
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
withPragmas :: Config -> [Located String] -> IO Config
---------------------------------------------------------------------------------------
withPragmas = foldM withPragma

withPragma :: Config -> Located String -> IO Config
withPragma c s = (c `mappend`) <$> parsePragma s

parsePragma   :: Located String -> IO Config
parsePragma s = withArgs [val s] $ cmdArgs config

---------------------------------------------------------------------------------------
-- | Monoid instances for updating options
---------------------------------------------------------------------------------------

instance Monoid Config where
  mempty        = Config def def def def def def def def def def def 2 def def def
  mappend c1 c2 = Config (sortNub $ files c1   ++     files          c2)
                         (sortNub $ idirs c1   ++     idirs          c2)
                         (diffcheck c1         ||     diffcheck      c2) 
                         (sortNub $ binders c1 ++     binders        c2) 
                         (noCheckUnknown c1    ||     noCheckUnknown c2) 
                         (notermination  c1    ||     notermination  c2) 
                         (nocaseexpand   c1    ||     nocaseexpand   c2) 
                         (strata         c1    ||     strata         c2) 
                         (notruetypes    c1    ||     notruetypes    c2) 
                         (totality       c1    ||     totality       c2) 
                         (noPrune        c1    ||     noPrune        c2) 
                         (maxParams      c1   `max`   maxParams      c2)
                         (smtsolver c1      `mappend` smtsolver      c2)
                         (shortNames c1        ||     shortNames     c2)
                         (ghcOptions c1        ++     ghcOptions     c2)

instance Monoid SMTSolver where
  mempty        = def
  mappend s1 s2 
    | s1 == s2  = s1 
    | s2 == def = s1 
    | otherwise = s2


------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

exitWithResult :: Config -> FilePath -> Maybe Output -> ErrorResult -> IO ErrorResult
exitWithResult cfg target o r = writeExit cfg target r $ fromMaybe emptyOutput o

writeExit cfg target r out
  = do {-# SCC "annotate" #-} annotate cfg target r (o_soln out) (o_annot out)
       donePhase Loud "annotate"
       let rs = showFix r
       writeCheckVars $ o_vars  out
       writeWarns     $ o_warns out
       writeResult (colorResult r) r
       writeFile   (extFileName Result target) rs
       return $ if null (o_warns out) then r else Unsafe []

writeWarns []            = return () 
writeWarns ws            = colorPhaseLn Angry "Warnings:" "" >> putStrLn (unlines $ nub ws)

writeCheckVars Nothing   = return ()
writeCheckVars (Just ns) = colorPhaseLn Loud "Checked Binders:" "" >> forM_ ns (putStrLn . dropModuleNames . showpp)

writeResult c            = mapM_ (writeDoc c) . zip [0..] . resDocs 
  where 
    writeDoc c (i, d)    = writeBlock c i $ lines $ render d
    writeBlock c _ []    = return ()
    writeBlock c 0 ss    = forM_ ss (colorPhaseLn c "")
    writeBlock c _ ss    = forM_ ("\n" : ss) putStrLn

resDocs Safe             = [text "SAFE"]
resDocs (Crash xs s)     = text ("CRASH: " ++ s) : pprManyOrdered "" {- "CRASH: " -} xs
resDocs (Unsafe xs)      = text "UNSAFE" : pprManyOrdered "" {- "UNSAFE: " -} (nub xs)
resDocs (UnknownError d) = [text "PANIC: Unexpected Error: " <+> d, reportUrl]
reportUrl                = text "Please submit a bug report at: https://github.com/ucsd-progsys/liquidhaskell"

instance Fixpoint (FixResult Error) where
  toFix = vcat . resDocs

------------------------------------------------------------------------
-- | Stuff To Output ---------------------------------------------------
------------------------------------------------------------------------

data Output = O { o_vars   :: Maybe [Name] 
                , o_warns  :: [String]
                , o_soln   :: FixSolution 
                , o_annot  :: !(AnnInfo Annot)
                }

emptyOutput = O Nothing [] M.empty mempty 
