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
  , extFileNameR
  , tempDirectory
  , extModuleName
  , withExt
  , isExtFile

  -- * Hardwired paths
  , getFixpointPath, getZ3LibPath

  -- * Various generic utility functions for finding and removing files
  -- , getHsTargets
  , getFileInDirs
  -- , findFileInDirs
  , copyFiles

) where

import qualified Control.Exception      as Ex
import           Control.Monad
import           Data.Functor           ((<$>))
import           Data.List              hiding (find)
import           Data.Maybe             (fromMaybe)
import           System.Directory
import           System.Environment
import           System.FilePath
-- import           System.FilePath.Find
import           Language.Fixpoint.Misc

------------------------------------------------------------
-- | Hardwired Paths and Files -----------------------------
------------------------------------------------------------

getFixpointPath = fromMaybe msg . msum <$>
                  sequence [ findExecutable "fixpoint.native"
                           , findExecutable "fixpoint.native.exe"
                           ]
  where msg     = errorstar "Cannot find fixpoint binary [fixpoint.native]"

getZ3LibPath    = dropFileName <$> getFixpointPath


checkM f msg p
  = do ex <- f p
       if ex then return p else errorstar $ "Cannot find " ++ msg ++ " at :" ++ p


-----------------------------------------------------------------------------------

data Ext = Cgi    -- ^ Constraint Generation Information
         | Fq     -- ^ Input to constraint solving (fixpoint)
         | Out    -- ^ Output from constraint solving (fixpoint)
         | Html   -- ^ HTML file with inferred type annotations
         | Annot  -- ^ Text file with inferred types
         | Vim    -- ^ Vim annotation file
         | Hs     -- ^ Haskell source
         | LHs    -- ^ Literate Haskell source
         | Js     -- ^ JavaScript source
         | Ts     -- ^ Typescript source
         | Spec   -- ^ Spec file (e.g. include/Prelude.spec)
         | Hquals -- ^ Qualifiers file (e.g. include/Prelude.hquals)
         | Result -- ^ Final result: SAFE/UNSAFE
         | Cst    -- ^ HTML file with templates?
         | Mkdn   -- ^ Markdown file (temporarily generated from .Lhs + annots)
         | Json   -- ^ JSON file containing result (annots + errors)
         | Saved  -- ^ Previous source (for incremental checking)
         | Cache  -- ^ Previous output (for incremental checking)
         | Pred
         | PAss
         | Dat
         | Smt2   -- ^ SMTLIB2 query file
         deriving (Eq, Ord, Show)

extMap e = go e
  where
    go Cgi    = ".cgi"
    go Pred   = ".pred"
    go PAss   = ".pass"
    go Dat    = ".dat"
    go Out    = ".fqout"
    go Fq     = ".fq"
    go Html   = ".html"
    go Cst    = ".cst"
    go Annot  = ".annot"
    go Vim    = ".vim.annot"
    go Hs     = ".hs"
    go LHs    = ".lhs"
    go Js     = ".js"
    go Ts     = ".ts"
    go Mkdn   = ".markdown"
    go Json   = ".json"
    go Spec   = ".spec"
    go Hquals = ".hquals"
    go Result = ".out"
    go Saved  = ".bak"
    go Cache  = ".err"
    go Smt2   = ".smt2"
    -- go _      = errorstar $ "extMap: Unknown extension " ++ show e

withExt         :: FilePath -> Ext -> FilePath
withExt f ext   =  replaceExtension f (extMap ext)

extFileName     :: Ext -> FilePath -> FilePath
extFileName e f = path </> addExtension file ext
  where
    path        = tempDirectory f
    file        = takeFileName  f
    ext         = extMap e

tempDirectory   :: FilePath -> FilePath
tempDirectory f
  | isTmp dir   = dir
  | otherwise   = dir </> tmpDirName
  where
    dir         = takeDirectory f
    isTmp       = (tmpDirName `isSuffixOf`)

tmpDirName      = ".liquid"

extFileNameR     :: Ext -> FilePath -> FilePath
extFileNameR ext = (`addExtension` extMap ext)

isExtFile ::  Ext -> FilePath -> Bool
isExtFile ext = (extMap ext ==) . takeExtension

extModuleName ::  String -> Ext -> FilePath
extModuleName modName ext =
  case explode modName of
    [] -> errorstar $ "malformed module name: " ++ modName
    ws -> extFileNameR ext $ foldr1 (</>) ws
  where
    explode = words . map (\c -> if c == '.' then ' ' else c)

copyFiles :: [FilePath] -> FilePath -> IO ()
copyFiles srcs tgt
  = do Ex.catch (removeFile tgt) $ \(_ :: Ex.IOException) -> return ()
       forM_ srcs (readFile >=> appendFile tgt)


----------------------------------------------------------------------------------

-- getHsTargets p = mapM canonicalizePath =<< files
--   where
--     files
--       | hasTrailingPathSeparator p = getHsSourceFiles p
--       | otherwise                  = return [p]

-- getHsSourceFiles = find dirs hs
--   where hs   = extension ==? ".hs" ||? extension ==? ".lhs"
--         dirs = liftM (not . ("dist" `isSuffixOf`)) directory

---------------------------------------------------------------------------


getFileInDirs :: FilePath -> [FilePath] -> IO (Maybe FilePath)
getFileInDirs name = findFirst (testM doesFileExist . (</> name))

-- findFileInDirs ::  FilePath -> [FilePath] -> IO FilePath
-- findFileInDirs file dirs
--   = liftM (fromMaybe err) (findFirst (find always (fileName ==? file)) dirs)
--     where err = errorstar $ "findFileInDirs: cannot find " ++ file ++ " in " ++ show dirs
