{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}

-- | This module contains all the code needed to output the result which 
--   is either: `SAFE` or `WARNING` with some reasonable error message when 
--   something goes wrong. All forms of errors/exceptions should go through 
--   here. The idea should be to report the error, the source position that 
--   causes it, generate a suitable .json file and then exit.


module Language.Haskell.Liquid.CmdLine (
   -- * Entry Command Line Options
   getOpts
   
   -- * Exit Function
  , exitWithResult

  -- * Extra Outputs
  , Output (..)
  
  ) where

import Control.DeepSeq
import Control.Monad
import Control.Applicative                      ((<$>))
import Data.Maybe
import Data.Monoid
import qualified Data.HashMap.Strict as M
import System.FilePath                          (dropFileName)
import System.Console.CmdArgs  hiding           (Loud)                
import System.Console.CmdArgs.Verbosity         (whenLoud)            

import Language.Fixpoint.Misc
import Language.Fixpoint.Files
import Language.Fixpoint.Types
import Language.Fixpoint.Names                  (dropModuleNames)

import Language.Fixpoint.Config hiding          (config, Config)
import Language.Haskell.Liquid.Types hiding     (typ)
import Language.Haskell.Liquid.Annotate
import Language.Haskell.Liquid.PrettyPrint

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
    = False 
          &= help "Incremental Checking: only check changed binders" 

 , binders
    = def &= help "Check a specific set of binders"

 , nofalse
    = def &= help "Remove false predicates from the refinements"

 , noPrune 
    = def &= help "Disable prunning unsorted Predicates"
          &= name "no-prune-unsorted"

 , notermination 
    = def &= help "Disable Termination Check"
          &= name "no-termination-check"

 , smtsolver 
    = def &= help "Name of SMT-Solver" 

 , noCheckUnknown 
    = def &= explicit
          &= name "no-check-unknown"
          &= help "Don't complain about specifications for unexported and unused values "

 , maxParams 
    = 2   &= help "Restrict qualifier mining to those taking at most `m' parameters (2 by default)"
 
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
             putStrLn $ copyright
             whenLoud $ putStrLn $ "liquid " ++ show args ++ "\n"
             mkOpts md

copyright = "LiquidHaskell © Copyright 2009-13 Regents of the University of California. All Rights Reserved.\n"

mkOpts :: Config -> IO Config
mkOpts md  
  = do files' <- sortNub . concat <$> mapM getHsTargets (files md) 
       idirs' <- if null (idirs md) then single <$> getIncludePath else return (idirs md) 
       return  $ md { files = files' } { idirs = map dropFileName files' ++ idirs' }
                                        -- tests fail if you flip order of idirs'


------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

exitWithResult :: FilePath -> Maybe Output -> ErrorResult -> IO ErrorResult
exitWithResult target o r = writeExit target r $ fromMaybe emptyOutput o

writeExit target r out   = do {-# SCC "annotate" #-} annotate target r (o_soln out) (o_annot out)
                              donePhase Loud "annotate"
                              let rs = showFix r
                              writeResult (colorResult r) r 
                              writeFile   (extFileName Result target) rs 
                              writeWarns     $ o_warns out 
                              writeCheckVars $ o_vars  out 
                              return r

writeWarns []            = return () 
writeWarns ws            = colorPhaseLn Angry "Warnings:" "" >> putStrLn (unlines ws)

writeCheckVars Nothing   = return ()
writeCheckVars (Just ns) = colorPhaseLn Loud "Checked Binders:" "" >> forM_ ns (putStrLn . dropModuleNames . showpp)

writeResult c            = mapM_ (writeDoc c) . resDocs 
  where 
    writeDoc c           = writeBlock c . lines . render
    writeBlock c (s:ss)  = do {colorPhaseLn c s ""; forM_ ss putStrLn }
    writeBlock c _       = return ()


resDocs Safe              = [text "SAFE"]
resDocs (Crash xs s)      = text ("CRASH: " ++ s) : pprManyOrdered "CRASH: " xs
resDocs (Unsafe xs)       = pprManyOrdered "UNSAFE: " xs
resDocs  (UnknownError d) = [text "PANIC: Unexpected Error: " <+> d, reportUrl]
reportUrl                 =      text "Please submit a bug report at:"
                            $+$  text "  https://github.com/ucsd-progsys/liquidhaskell"

instance Fixpoint (FixResult Error) where
  toFix = vcat . resDocs

  -- vcat [[String]]
  -- toFix Safe             = text "SAFE"
  -- toFix (UnknownError d) = text "Unknown Error!"
  -- toFix (Crash xs msg)   = vcat $ text "Crash!"  : pprManyOrdered "CRASH:   " xs ++ [parens (text msg)] 
  -- toFix (Unsafe xs)      = vcat $ text "Unsafe:" : pprManyOrdered "WARNING: " xs


------------------------------------------------------------------------
-- | Stuff To Output ---------------------------------------------------
------------------------------------------------------------------------

data Output = O { o_vars   :: Maybe [Name] 
                , o_warns  :: [String]
                , o_soln   :: FixSolution 
                , o_annot  :: !(AnnInfo Annot)
                }

emptyOutput = O Nothing [] M.empty mempty 
