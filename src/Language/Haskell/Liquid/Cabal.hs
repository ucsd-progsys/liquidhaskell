-- | This module contains a single function that extracts the cabal information about a target file, if any.
--   This information can be used to extend the source-directories that are searched to find modules that are
--   imported by the target file.

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--cabaldir"       @-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE CPP                  #-}

module Language.Haskell.Liquid.Cabal (cabalInfo, Info(..)) where

import Control.Applicative ((<$>))
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Configuration
import Distribution.PackageDescription.Parse
import Distribution.Simple.BuildPaths
import Distribution.System
import Distribution.Verbosity
import Language.Haskell.Extension
import System.Console.CmdArgs
import System.Environment
import System.Exit
import System.FilePath
import System.Directory
import System.Info
import Language.Haskell.Liquid.Errors

-- To use in ghci:
--   exitWithPanic = undefined

-----------------------------------------------------------------------------------------------
cabalInfo :: FilePath -> IO (Maybe Info)
-----------------------------------------------------------------------------------------------
cabalInfo f = do
  f  <- canonicalizePath f
  cf <- findCabalFile f
  case cf of
    Just f  -> Just  <$> processCabalFile f
    Nothing -> return Nothing

processCabalFile :: FilePath -> IO Info
processCabalFile f = do
  i <- cabalConfiguration f <$> readPackageDescription silent f
  i <- addPackageDbs i
  whenLoud $ putStrLn $ "Cabal Info: " ++ show i
  return i

-----------------------------------------------------------------------------------------------
findCabalFile :: FilePath -> IO (Maybe FilePath)
-----------------------------------------------------------------------------------------------
findCabalFile = fmap listToMaybe . findInPath isCabal
  where
    isCabal   = (".cabal" ==) . takeExtension

findInPath :: (FilePath -> Bool) -> FilePath -> IO [FilePath]
findInPath p f = concat <$> mapM (findInDir p) (ancestorDirs f)

ancestorDirs :: FilePath -> [FilePath]
ancestorDirs = go . takeDirectory
  where
    go f
      | f == f'   = [f]
      | otherwise = f : go f'
      where
        f'        = takeDirectory f

findInDir :: (FilePath -> Bool) -> FilePath -> IO [FilePath]
findInDir p dir = do
  files <- getDirectoryContents dir
  return [ dir </> f | f <- files, p f ]

-----------------------------------------------------------------------------------------------

data Info = Info { cabalFile    :: FilePath
                 , buildDirs    :: [FilePath]
                 , sourceDirs   :: [FilePath]
                 , exts         :: [Extension]
                 , otherOptions :: [String]
                 , packageDbs   :: [String]
                 , packageDeps  :: [String]
                 } deriving (Show)


addPackageDbs :: Info -> IO Info
addPackageDbs i = maybe i addDB <$> getSandboxDB i
  where
    addDB db    = i { packageDbs = T.unpack db : packageDbs i}

getSandboxDB :: Info -> IO (Maybe T.Text)
getSandboxDB i = do
  tM <- maybeReadFile $ sandBoxFile i
  case tM of
   Just t  -> return $ Just $ parsePackageDb t
   Nothing -> return Nothing
   -- fmap <$> maybeReadFile (sandBoxFile i)

parsePackageDb :: T.Text -> T.Text
parsePackageDb t = case dbs of
                    [db] -> T.strip db
                    _    -> exitWithPanic $ "Malformed package-db in sandbox: " ++ show dbs
                   where
                     dbs = mapMaybe (T.stripPrefix pfx) $ T.lines t
                     pfx = "package-db:"
    -- /Users/rjhala/research/liquid/liquidhaskell/.cabal-sandbox/x86_64-osx-ghc-7.8.3-packages.conf.d

maybeReadFile :: FilePath -> IO (Maybe T.Text)
maybeReadFile f = do
  b <- doesFileExist f
  if b then Just <$> TIO.readFile f
       else return Nothing



sandBoxFile :: Info -> FilePath
sandBoxFile i = dir </> "cabal.sandbox.config"
  where
    dir       = takeDirectory $ cabalFile i


dumpPackageDescription :: PackageDescription -> FilePath -> Info
dumpPackageDescription pkgDesc file = Info {
    cabalFile    = file
  , buildDirs    = nub (normalise <$> getBuildDirectories pkgDesc dir)
  , sourceDirs   = nub (normalise <$> getSourceDirectories buildInfo dir)
  , exts         = nub (concatMap usedExtensions buildInfo)
  , otherOptions = nub (filter isAllowedOption (concatMap (hcOptions GHC) buildInfo))
  , packageDbs   = []
  , packageDeps  = nub [ unPackName n | Dependency n _ <- buildDepends pkgDesc, n /= thisPackage ]
  }
  where
    buildInfo    = allBuildInfo pkgDesc
    dir          = dropFileName file
    thisPackage  = (pkgName . package) pkgDesc

unPackName :: PackageName -> String
unPackName (PackageName s) = s


getSourceDirectories :: [BuildInfo] -> FilePath -> [String]
getSourceDirectories buildInfo cabalDir = map (cabalDir </>) (concatMap hsSourceDirs buildInfo)

allowedOptions :: [String]
allowedOptions =
  ["-W"
  ,"-w"
  ,"-Wall"
  ,"-fglasgow-exts"
  ,"-fpackage-trust"
  ,"-fhelpful-errors"
  ,"-F"
  ,"-cpp"]

allowedOptionPrefixes :: [String]
allowedOptionPrefixes =
  ["-fwarn-"
  ,"-fno-warn-"
  ,"-fcontext-stack="
  ,"-firrefutable-tuples"
  ,"-D"
  ,"-U"
  ,"-I"
  ,"-fplugin="
  ,"-fplugin-opt="
  ,"-pgm"
  ,"-opt"]


getBuildDirectories :: PackageDescription -> FilePath -> [String]
getBuildDirectories pkgDesc dir =
  case library pkgDesc of
    Just _ -> buildDir : buildDirs
    Nothing -> buildDirs
  where
    distDir        = dir </> defaultDistPref
    buildDir       = distDir </> "build"
    autogenDir     = buildDir </> "autogen"
    execBuildDir e = buildDir </> exeName e </> (exeName e ++ "-tmp")
    buildDirs      = autogenDir : map execBuildDir (executables pkgDesc)

isAllowedOption :: String -> Bool
isAllowedOption opt = elem opt allowedOptions || any (`isPrefixOf` opt) allowedOptionPrefixes

buildCompiler :: CompilerId
buildCompiler = CompilerId buildCompilerFlavor compilerVersion

cabalConfiguration :: FilePath -> GenericPackageDescription -> Info
cabalConfiguration cabalFile desc =
  case finalizePackageDescription []
                                  (const True)
                                  buildPlatform
#if MIN_VERSION_Cabal(1,22,0)
                                  (unknownCompilerInfo buildCompiler NoAbiTag)
#else
                                  buildCompiler
#endif
                                  []
                                  desc of
       Right (pkgDesc,_) -> dumpPackageDescription pkgDesc cabalFile
       Left e -> exitWithPanic $ "Issue with package configuration\n" ++ show e

