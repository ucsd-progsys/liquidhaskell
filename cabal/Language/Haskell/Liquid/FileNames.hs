
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.FileNames ( 
    tagName , dummyName, preludeName, boolConName, listConName, tupConName, vvName 
  , Ext (..), repFileName, extFileName, extModuleName, isExtFile
  , getHsTargets
  --, fqName, outName , cgiName, htmlName, annotName, libName, cstName
  , getFileInDirs, findFileInDirs
  , getIncludePath, resolvePath
  , copyFiles, deleteBinFiles
) where

import Text.Printf (printf)
import Control.Monad.State
import qualified Control.Exception as Ex
import System.Directory
import System.FilePath
import System.FilePath.Find


import System.Environment
import qualified Data.Map as M
import Data.List 
import Debug.Trace (trace)
import Data.Maybe
import Control.DeepSeq
import Language.Haskell.Liquid.Misc

------------------------------------------------------------
---------------- IO/Paths/Flags/Constants ------------------
------------------------------------------------------------

envVarName = "LIQUIDHS"
envPrefix  = "$" ++ envVarName ++ "/"

getIncludePath ::  IO String
getIncludePath = getEnv envVarName 



data Ext = Cgi | Out | Fq | Html | Cst | Annot | LHs | Hs | Spec | Hquals | Pred | PAss| Dat
           deriving (Eq, Ord)

extMap   = M.fromList [ (Cgi,    "cgi")
                      , (Pred,   "pred")
                      , (PAss,   "pass")
                      , (Dat,    "dat")
                      , (Out,    "out")
                      , (Fq,     "fq")
                      , (Html,   "html")
                      , (Cst,    "cst")
                      , (Annot,  "annot")
                      , (Hs,     "hs")
                      , (LHs,    "lhs")
                      , (Spec,   "spec")
                      , (Hquals, "hquals") ]

repFileName     :: Ext -> FilePath -> FilePath
repFileName ext = extFileName ext . dropFileName 

extFileName     :: Ext -> FilePath -> FilePath
extFileName ext = (`addExtension` (extMap M.! ext))

isExtFile ::  Ext -> FilePath -> Bool
isExtFile ext = ((extMap M.! ext) `isSuffixOf`)

extModuleName ::  String -> Ext -> FilePath
extModuleName modName ext = 
  case explode modName of 
    [] -> errorstar $ "malformed module name: " ++ modName
    ws -> extFileName ext $ foldr1 (</>) ws
  where explode = words . map (\c -> if c == '.' then ' ' else c)

preludeName  :: String
preludeName  = "Prelude"

libName      :: String -> FilePath
libName ext  = envPrefix ++ "Prelude." ++ ext

existingFiles :: String -> [FilePath] -> IO [FilePath]
existingFiles = filterM . warnMissing

warnMissing s f 
  = do b <- doesFileExist f
       unless b $ putStrLn $ printf "WARNING: missing file (%s): %s" s f
       return b

copyFiles :: [FilePath] -> FilePath -> IO ()
copyFiles srcs tgt 
  = do Ex.catch (removeFile tgt) $ \(e :: Ex.IOException) -> return () 
       forM_ srcs $ (readFile >=> appendFile tgt)

deleteBinFiles :: FilePath -> IO ()
deleteBinFiles fn = mapM_ (tryIgnore "delete binaries" . removeFile) 
                  $ (fn `replaceExtension`) `fmap` exts
  where exts = ["hi", "o"]

retry ::  IOError -> [IO a] -> IO a
retry err []     = ioError err
retry err (a:as) = Ex.catch a $ \(e :: Ex.IOException) -> retry err as

resolvePath :: FilePath -> FilePath -> IO FilePath
resolvePath base path
  = case stripPrefix envPrefix path of
      Just path' -> liftM (</> path') getIncludePath
      Nothing    -> return $ if isAbsolute path then path else (base </> path) 


----------------------------------------------------------------------------------

getHsTargets p 
  | hasTrailingPathSeparator p = getHsSourceFiles p
  | otherwise                  = return [p]

getHsSourceFiles = System.FilePath.Find.find dirs hs 
  where hs   = extension ==? ".hs" ||? extension ==? ".lhs"
        dirs = liftM (not . ("dist" `isSuffixOf`)) directory

---------------------------------------------------------------------------


getFileInDirs :: FilePath -> [FilePath] -> IO (Maybe FilePath)
getFileInDirs name dirs = findFirst (testM doesFileExist . (</> name)) dirs


findFileInDirs ::  FilePath -> [FilePath] -> IO FilePath
findFileInDirs file dirs
  = do p <- findFirst (System.FilePath.Find.find always (fileName ==? file)) dirs
       case p of
         Just p -> return p
         Nothing -> errorstar $ "findFileInDirs: cannot find " ++ file ++ " in " ++ show dirs


----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

dummyName   = "_LIQUID_dummy"
tagName     = "TAG"
boolConName = "Bool"
listConName = "List"
tupConName  = "Tuple"
vvName      = "VV"
