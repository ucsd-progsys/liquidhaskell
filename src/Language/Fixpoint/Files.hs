{-# LANGUAGE ScopedTypeVariables #-}

-- | This module contains Haskell variables representing globally visible 
-- names for files, paths, extensions.
--
-- Rather than have strings floating around the system, all constant names
-- should be defined here, and the (exported) variables should be used and
-- manipulated elsewhere.

module Language.Fixpoint.Files (
  
  -- * Hardwired file extension names
    Ext (..)
  , extFileName
  , extModuleName
  , isExtFile
 
  -- * Hardwired paths 
  , getIncludePath, getFixpointPath, getHqBotPath, getZ3LibPath, getCSSPath

  -- * Various generic utility functions for finding and removing files
  , getHsTargets
  , getFileInDirs
  , findFileInDirs
  , copyFiles, deleteBinFiles
  
) where

import qualified Control.Exception            as Ex
-- import           Control.Monad.State
import           Control.Monad -- .State
import           Data.Functor                 ((<$>))
import           Data.List                    hiding (find)
import           Data.Maybe                   (fromMaybe)
import           System.Directory
import           System.Environment
import           System.FilePath
import           System.FilePath.Find
import           Language.Fixpoint.Misc

------------------------------------------------------------
-- | Hardwired Paths and Files -----------------------------
------------------------------------------------------------

envVarName = "LIQUIDHS"

getIncludePath, getHqBotPath, getCSSPath, getFixpointPath  ::  IO FilePath 

getIncludePath  = getSuffixPath ["include"]                                 >>= checkM doesDirectoryExist "include directory"
getCSSPath      = getSuffixPath ["syntax", "liquid.css"]                    >>= checkM doesFileExist      "css file"          
-- getFixpointPath = getSuffixPath ["external", "fixpoint", "fixpoint.native"] >>= checkM doesFileExist      "fixpoint binary"   

getFixpointPath = fromMaybe msg <$> findExecutable "fixpoint.native"
  where msg     = errorstar "Cannot find fixpoint binary [fixpoint.native]"

getHqBotPath = liftM (`combine` "Bot.hquals") getIncludePath
-- getZ3LibPath    = do p <- dropFileName <$> getFixpointPath 
--                      return $ joinPath [p, "external", "z3", "lib"] 

getZ3LibPath    = dropFileName <$> getFixpointPath 



getSuffixPath ::  [FilePath] -> IO FilePath 
getSuffixPath suff 
  = (joinPath . (: suff)) `fmap` getEnv envVarName

checkM f msg p 
  = do ex <- f p
       if ex then return p else errorstar $ "Cannot find " ++ msg ++ " at :" ++ p

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
         | Result -- ^ Final result: SAFE/UNSAFE
         | Cst    -- ^ I've totally forgotten!
         | Mkdn   -- ^ Markdown file (temporarily generated from .Lhs + annots) 
         | Pred   
         | PAss    
         | Dat    
         deriving (Eq, Ord, Show)

extMap e = go e
  where 
    go Cgi    = "cgi"
    go Pred   = "pred"
    go PAss   = "pass"
    go Dat    = "dat"
    go Out    = "fqout"
    go Fq     = "fq"
    go Html   = "html"
    go Cst    = "cst"
    go Annot  = "annot"
    go Hs     = "hs"
    go LHs    = "lhs"
    go Mkdn   = "markdown"
    go Spec   = "spec"
    go Hquals = "hquals" 
    go Result = "out"
    go _      = errorstar $ "extMap: Unknown extension" ++ show e

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

copyFiles :: [FilePath] -> FilePath -> IO ()
copyFiles srcs tgt
  = do Ex.catch (removeFile tgt) $ \(_ :: Ex.IOException) -> return ()
       forM_ srcs (readFile >=> appendFile tgt)

deleteBinFiles :: FilePath -> IO ()
deleteBinFiles fn = mapM_ (tryIgnore "delete binaries" . removeFile)
                  $ (fn `replaceExtension`) `fmap` exts
  where exts = ["hi", "o"]


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
