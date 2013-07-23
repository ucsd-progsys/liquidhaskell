{-# LANGUAGE TupleSections, DeriveDataTypeable #-}

module Language.Haskell.Liquid.CmdLine (getOpts) where

import Control.Applicative                      ((<$>))
import System.FilePath                          (dropFileName)
import Language.Fixpoint.Misc                   (single, sortNub) 
import Language.Fixpoint.Files                  (getHsTargets, getIncludePath)
import Language.Fixpoint.Config hiding          (config, Config)
import Language.Haskell.Liquid.Types
import System.Console.CmdArgs                  

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
   
 , incCheck 
    = false 
          &= help "Incremental Checking: only check changed binders" 

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
             putStrLn $ banner md
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

