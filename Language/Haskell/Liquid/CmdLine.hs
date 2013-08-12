{-# LANGUAGE TupleSections, DeriveDataTypeable #-}

module Language.Haskell.Liquid.CmdLine (
  -- * Get Command Line Configuration 
  getOpts
  
  -- * Update Configuration With Pragma
  , withPragmas
  ) where

import Control.Monad                            (foldM)
import Control.Applicative                      ((<$>))

import System.Environment                       (withArgs)
import System.FilePath                          (dropFileName)
import Language.Fixpoint.Misc                   (single, sortNub) 
import Language.Fixpoint.Files                  (getHsTargets, getIncludePath)
import Language.Fixpoint.Config hiding          (config, Config)
import Language.Haskell.Liquid.Types hiding     (config)
import Language.Fixpoint.Types hiding           (config)
import System.Console.CmdArgs                  
import System.Console.CmdArgs.Verbosity                  
import Data.List                                (foldl')
import Data.Monoid

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
   &= summary "LiquidHaskell © Copyright 2009-13 Regents of the University of California." 
   &= details [ "LiquidHaskell is a Refinement Type based verifier for Haskell"
              , ""
              , "To check a Haskell file foo.hs, type:"
              , "  liquid foo.hs "
              ]

getOpts :: IO Config 
getOpts = do md <- cmdArgs config 
             whenLoud $ putStrLn $ banner md
             mkOpts md

banner args =  "LiquidHaskell © Copyright 2009-13 Regents of the University of California.\n" 
            ++ "All Rights Reserved.\n"
            ++ "liquid " ++ show args ++ "\n" 

mkOpts :: Config -> IO Config
mkOpts md  
  = do files' <- sortNub . concat <$> mapM getHsTargets (files md) 
       idirs' <- if null (idirs md) then single <$> getIncludePath else return (idirs md) 
       return  $ md { files = files' } { idirs = map dropFileName files' ++ idirs' }
                                        -- tests fail if you flip order of idirs'




---------------------------------------------------------------------------------------
withPragmas :: Config -> [Located String] -> IO Config
---------------------------------------------------------------------------------------
withPragmas = foldM withPragma

withPragma :: Config -> Located String -> IO Config
withPragma c s = (c `mappend`) <$> parsePragma s

parsePragma   :: Located String -> IO Config
parsePragma s = withArgs [val s] $ cmdArgs config

---------------------------------------------------------------------------------------
-- Monoid instances for updating options
---------------------------------------------------------------------------------------

instance Monoid Config where
  mempty        = Config def def def def def def def def 2 def
  mappend c1 c2 = Config (sortNub $ files c1   ++     files          c2)
                         (sortNub $ idirs c1   ++     idirs          c2)
                         (diffcheck c1         ||     diffcheck      c2) 
                         (sortNub $ binders c1 ++     binders        c2) 
                         (noCheckUnknown c1    ||     noCheckUnknown c2) 
                         (nofalse        c1    ||     nofalse        c2) 
                         (notermination  c1    ||     notermination  c2) 
                         (noPrune        c1    ||     noPrune        c2) 
                         (maxParams      c1   `max`   maxParams      c2)
                         (smtsolver c1      `mappend` smtsolver      c2)

instance Monoid SMTSolver where
  mempty        = def
  mappend s1 s2 
    | s1 == s2  = s1 
    | s2 == def = s1 
    | otherwise = s2


