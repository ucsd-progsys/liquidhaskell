{-# LANGUAGE TupleSections, DeriveDataTypeable #-}

module Language.Haskell.Liquid.CmdLine (getOpts) where

import System.Environment                       (getArgs)
import System.Console.GetOpt

-- import System.Console.CmdArgs
import Control.Monad                            (liftM, liftM2)
import Language.Haskell.Liquid.FileNames        (getHsTargets)
import Language.Haskell.Liquid.Misc             (errorstar, sortNub)
import Language.Haskell.Liquid.FileNames        (getIncludePath)
import System.FilePath                          (dropFileName)

------------------------------------------------------------------------------
---------- Old Fashioned, Using getopts --------------------------------------
------------------------------------------------------------------------------

getOpts :: IO ([FilePath], [FilePath]) 
getOpts
  = do args <- getArgs
       putStrLn $ banner args
       case getOpt RequireOrder options args of
         (flags, targets, []) -> mkOpts flags targets
         (_,     _,     msgs) -> errorstar $ concat msgs ++ usageInfo header options

mkOpts :: [Flag] -> [String] -> IO ([FilePath], [FilePath])
mkOpts flags targets 
  = do files <- liftM (sortNub . concat) $ mapM getHsTargets targets
       idirs <- if null flags then liftM (:[]) getIncludePath else return [d | IDir d <- flags]
       return (files, [dropFileName f | f <- files] ++ idirs)


data Flag = IDir FilePath
  deriving (Eq, Show)

options :: [OptDescr Flag]
options = [ Option ['i'] ["include"] (ReqArg IDir "PATH") "Include Directory" ] 

header = "Usage: liquid [OPTION...] file\n" ++ 
         "Usage: liquid [OPTION...] dir" 

banner args =  "© Copyright 2009-12 Regents of the University of California.\n" 
            ++ "All Rights Reserved.\n"
            ++ "liquid " ++ show args ++ "\n" 


-------------------------------------------------------------------------------
--- Using cmdargs, seems to not like my ghc version ---------------------------
-------------------------------------------------------------------------------

--getOpts_ :: IO ([FilePath], FilePath) 
--getOpts_ 
--  = do md <- cmdArgsRun mode 
--       case md of
--         File f d -> return ([f], "") --liftM  ([f],) (getIdir d) 
--         Path p d -> return ([], "") --liftM2 (,)    (getHsSourceFiles p) (getIdir d)
--
--getIdir o = case o of
--              Just p  -> return p
--              Nothing -> getIncludePath
--
--mode = cmdArgsMode $ modes [optFile, optPath] 
--                   &= help "Liquid Types For Haskell" 
--                   &= summary "liquid v0.0.0 (C) Regents of The University of California" 
--                   &= program "liquid"
--
--data LModes 
--  = File { file :: FilePath, idir :: Maybe FilePath } 
--  | Path { path :: FilePath, idir :: Maybe FilePath }
--    deriving (Data, Typeable, Show, Eq)
--
--optIdir = Nothing &= name "i" &= help "Include Directory (for .spec files)" 
--
--optFile = File { file = def &= help "Source File" &= typFile
--               , idir = optIdir 
--               }
--
--optPath = Path { path = def &= help "Source path to be recursively trawled" &= typDir 
--               , idir = optIdir 
--               }


