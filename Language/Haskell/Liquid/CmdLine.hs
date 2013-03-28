{-# LANGUAGE TupleSections, DeriveDataTypeable #-}

module Language.Haskell.Liquid.CmdLine (getOpts) where

import System.Environment                       (getArgs)
import System.Console.GetOpt

-- import System.Console.CmdArgs
import Control.Monad                            (liftM, liftM2)
import System.FilePath                          (dropFileName)

import Language.Fixpoint.Misc                   (errorstar, sortNub)
import Language.Fixpoint.Files                  (getHsTargets, getIncludePath)
import Language.Haskell.Liquid.Types
import System.Console.CmdArgs                  

------------------------------------------------------------------------------
---------- Old Fashioned, Using getopts --------------------------------------
------------------------------------------------------------------------------

-- getOpts :: IO ([FilePath], [FilePath]) 
-- getOpts
--   = do args <- getArgs
--        putStrLn $ banner args
--        case getOpt RequireOrder options args of
--          (flags, targets, []) -> mkOpts [ d | IDir d <- flags ] targets
--          (_,     _,     msgs) -> errorstar $ concat msgs ++ usageInfo header options
-- 
-- 
-- data Flag = IDir FilePath
--   deriving (Eq, Show)
-- 
-- options :: [OptDescr Flag]
-- options = [ Option ['i'] ["include"] (ReqArg IDir "PATH") "Include Directory" ] 
-- 
-- header = "Usage: liquid [OPTION...] file\n" ++ 
--          "Usage: liquid [OPTION...] dir" 

banner args =  "LiquidHaskell © Copyright 2009-13 Regents of the University of California.\n" 
            ++ "All Rights Reserved.\n"
            ++ "liquid " ++ show args ++ "\n" 

mkOpts :: [FilePath] -> [FilePath] -> IO ([FilePath], [FilePath])
mkOpts flags targets 
  = do files <- liftM (sortNub . concat) $ mapM getHsTargets targets
       idirs <- if null flags then liftM (:[]) getIncludePath else return flags
       return (files, [dropFileName f | f <- files] ++ idirs)

-------------------------------------------------------------------------------
--- Using cmdargs, seems to not like my ghc version ---------------------------
-------------------------------------------------------------------------------

config = Config { 
   files = def &= typ "TARGET" 
               &= args 
               &= typFile 
 
 , idirs = def &= typDir 
               &= help "Paths to Spec Include Directory " 
 
 , binds = def &= help "Top-level binders to verify (DEFAULT = all)" 
 
 } &= verbosity 
   &= program "liquid" 
   &= help    "Refinement Types for Haskell" 
   &= summary "LiquidHaskell © Copyright 2009-13 Regents of the University of California." 
   &= details [ "LiquidHaskell is a Refinement Type based verifier for Haskell"
              , ""
              , "To check a Haskell file foo.hs, type:"
              , "  liquid foo.hs "
              ]

getOpts :: IO ([FilePath], [FilePath])
getOpts = do md <- cmdArgs config 
             putStrLn $ banner md
             mkOpts (idirs md) (files md)

