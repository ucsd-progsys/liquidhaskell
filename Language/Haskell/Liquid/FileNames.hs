{-# LANGUAGE ScopedTypeVariables #-}

-- | This module contains Haskell variables representing globally visible 
-- names for files, paths, extensions and various other constants. 
-- Rather than have strings floating around the system, all constant names
-- should be defined here, and the (exported) variables should be used and
-- manipulated elsewhere.

module Language.Haskell.Liquid.FileNames (
  
  -- * Hardwired file extension names
    Ext (..)
  , repFileName
  , extFileName
  , extModuleName
  , isExtFile
 
  -- * Hardwired global names 
  , dummyName
  , preludeName
  , boolConName
  , listConName
  , tupConName
  , vvName
  
  -- * Hardwired paths 
  , getIncludePath, getFixpointPath, getCSSPath

  -- * Various generic utility functions for finding and removing files
  , getHsTargets
  , getFileInDirs
  , findFileInDirs
  , copyFiles, deleteBinFiles
  
) where

import qualified Control.Exception            as Ex
import           Control.Monad.State
import           Data.List                    hiding (find)
import qualified Data.Map                     as M
import           Data.Maybe                   (fromMaybe)
import           Language.Haskell.Liquid.Misc
import           System.Directory
import           System.Environment
import           System.FilePath
import           System.FilePath.Find

------------------------------------------------------------
-- | Hardwired Paths and Files -----------------------------
------------------------------------------------------------

envVarName = "LIQUIDHS"

getIncludePath, getCSSPath, getFixpointPath  ::  IO FilePath 

getIncludePath  = getSuffixPath ["include"]                                 >>= checkM doesDirectoryExist "include directory"
getCSSPath      = getSuffixPath ["syntax", "hscolour.css"]                  >>= checkM doesFileExist      "css file"          
getFixpointPath = getSuffixPath ["external", "fixpoint", "fixpoint.native"] >>= checkM doesFileExist      "fixpoint binary"   


getSuffixPath ::  [FilePath] -> IO FilePath 
getSuffixPath suff 
  = (joinPath . (: suff)) `fmap` getEnv envVarName

checkM f msg p 
  = do ex <- f p
       if ex then return p else errorstar $ "Cannot find " ++ msg ++ " at :" ++ p

-- getIncludePath  = checkM doesDirectoryExist "include directory" =<< getSuffixPath ["include"]
-- getCSSPath      = checkM doesFileExist      "css file"          =<< getSuffixPath ["syntax", "hscolour.css"]
-- getFixpointPath = checkM doesFileExist      "fixpoint binary"   =<< getSuffixPath ["external", "fixpoint", "fixpoint.native"]

-- envPrefix  = "$" ++ envVarName ++ "/"
-- getIncludePath  = (</> "include") `fmap` getEnv envVarName
-- getFixpointPath ::  IO FilePath 
-- getFixpointPath = do p  <- getSuffixPath ["external", "fixpoint", "fixpoint.native"]
--                      ex <- doesFileExist p
--                      if ex then return p else err p
--                   where err p   = errorstar $ "Cannot find fixpoint executable at: " ++ p

-- checkExists msg p 
--   = do ex <- doesFileExist p
--        if ex then return p else err
--     where err = errorstar $ "Cannot find " ++ msg ++ " at :" ++ p


-----------------------------------------------------------------------------------

data Ext = Cgi    -- ^ Constraint Generation Information 
         | Fq     -- ^ Input to constraint solving (fixpoint)
         | Out    -- ^ Output from constraint solving (fixpoint)
         | Html   -- ^ HTML file with inferred type annotations 
         | Annot  -- ^ Text file with inferred types 
         | Hs     -- ^ Target source 
         | LHs    -- ^ Literate Haskell target source file
         | Spec   -- ^ Spec file (e.g. include/Prelude.spec) 
         | Hquals -- ^ Qualifiers file (e.g. include/Prelude.hquals)
         | Cst    -- ^ I've totally forgotten!
         | Mkdn   -- ^ Markdown file (temporarily generated from .Lhs + annots) 
         | Pred   
         | PAss    
         | Dat    
         deriving (Eq, Ord, Show)

extMap Cgi    = "cgi"
extMap Pred   = "pred"
extMap PAss   = "pass"
extMap Dat    = "dat"
extMap Out    = "out"
extMap Fq     = "fq"
extMap Html   = "html"
extMap Cst    = "cst"
extMap Annot  = "annot"
extMap Hs     = "hs"
extMap LHs    = "lhs"
extMap Mkdn   = "md"
extMap Spec   = "spec"
extMap Hquals = "hquals" 
extMap e      = errorstar $ "extMap: Unknown extension" ++ show e


-- extMap   = M.fromList [ (Cgi,    "cgi")
--                       , (Pred,   "pred")
--                       , (PAss,   "pass")
--                       , (Dat,    "dat")
--                       , (Out,    "out")
--                       , (Fq,     "fq")
--                       , (Html,   "html")
--                       , (Cst,    "cst")
--                       , (Annot,  "annot")
--                       , (Hs,     "hs")
--                       , (LHs,    "lhs")
--                       , (Mkdn,   "md")
--                       , (Spec,   "spec")
--                       , (Hquals, "hquals") ]



repFileName     :: Ext -> FilePath -> FilePath
repFileName ext = extFileName ext . dropFileName

extFileName     :: Ext -> FilePath -> FilePath
extFileName ext = (`addExtension` (extMap ext))

isExtFile ::  Ext -> FilePath -> Bool
isExtFile ext = ((extMap ext) `isSuffixOf`)

extModuleName ::  String -> Ext -> FilePath
extModuleName modName ext =
  case explode modName of
    [] -> errorstar $ "malformed module name: " ++ modName
    ws -> extFileName ext $ foldr1 (</>) ws
  where explode = words . map (\c -> if c == '.' then ' ' else c)

preludeName  :: String
preludeName  = "Prelude"

copyFiles :: [FilePath] -> FilePath -> IO ()
copyFiles srcs tgt
  = do Ex.catch (removeFile tgt) $ \(_ :: Ex.IOException) -> return ()
       forM_ srcs (readFile >=> appendFile tgt)

deleteBinFiles :: FilePath -> IO ()
deleteBinFiles fn = mapM_ (tryIgnore "delete binaries" . removeFile)
                  $ (fn `replaceExtension`) `fmap` exts
  where exts = ["hi", "o"]

-- resolvePath :: FilePath -> FilePath -> IO FilePath
-- resolvePath base path
--   = case stripPrefix envPrefix path of
--       Just path' -> liftM (</> path') getIncludePath
--       Nothing    -> return $ if isAbsolute path then path else base </> path

-- libName      :: String -> FilePath
-- libName ext  = envPrefix ++ "Prelude." ++ ext

-- existingFiles :: String -> [FilePath] -> IO [FilePath]
-- existingFiles = filterM . warnMissing

-- warnMissing s f
--   = do b <- doesFileExist f
--        unless b $ putStrLn $ printf "WARNING: missing file (%s): %s" s f
--        return b



----------------------------------------------------------------------------------

getHsTargets p
  | hasTrailingPathSeparator p = getHsSourceFiles p
  | otherwise                  = return [p]

getHsSourceFiles = find dirs hs
  where hs   = extension ==? ".hs" ||? extension ==? ".lhs"
        dirs = liftM (not . ("dist" `isSuffixOf`)) directory

---------------------------------------------------------------------------


getFileInDirs :: FilePath -> [FilePath] -> IO (Maybe FilePath)
getFileInDirs name = findFirst (testM doesFileExist . (</> name))

findFileInDirs ::  FilePath -> [FilePath] -> IO FilePath
findFileInDirs file dirs
  = liftM (fromMaybe err) (findFirst (find always (fileName ==? file)) dirs)
    where err = errorstar $ "findFileInDirs: cannot find " ++ file ++ " in " ++ show dirs


----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

dummyName   = "_LIQUID_dummy"
-- tagName     = "TAG"
boolConName = "Bool"
listConName = "List"
tupConName  = "Tuple"
vvName      = "VV"
