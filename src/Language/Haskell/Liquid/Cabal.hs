-- | This module contains a single function that extracts the cabal information about a target file, if any.
--   This information can be used to extend the source-directories that are searched to find modules that are
--   imported by the target file.

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Cabal (cabalInfo) where

import Control.Applicative ((<$>))
import Data.List
import Data.Maybe
import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Configuration
import Distribution.PackageDescription.Parse
import Distribution.Simple.BuildPaths
import Distribution.System
import Distribution.Verbosity
import Language.Haskell.Extension
import System.Environment
import System.Exit
import System.FilePath
import System.Directory
import System.Info

-----------------------------------------------------------------------------------------------
cabalInfo :: FilePath -> IO (Maybe Info)
-----------------------------------------------------------------------------------------------
cabalInfo f = do
  cf <- findCabalFile f
  case cf of
    Just f  -> processCabalFile f
    Nothing -> return Nothing

processCabalFile :: FilePath -> IO (Maybe Info)
processCabalFile f = extract . cabalConfiguration f <$> readPackageDescription silent f
  where
    extract        = either (const Nothing) Just

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

data Info = Info { cabalDir     :: FilePath
                 , cabalFile    :: FilePath
                 , buildDirs    :: [FilePath]
                 , sourceDirs   :: [FilePath]
                 , exts         :: [Extension]
                 , otherOptions :: [String]
                 } deriving (Show)

dumpPackageDescription :: PackageDescription -> FilePath -> Info
dumpPackageDescription pkgDesc file = Info {
    cabalDir     = dir
  , cabalFile    = file
  , buildDirs    = nub (normalise <$> getBuildDirectories pkgDesc dir)
  , sourceDirs   = nub (normalise <$> getSourceDirectories buildInfo dir)
  , exts         = nub (concatMap usedExtensions buildInfo)
  , otherOptions = nub (filter isAllowedOption (concatMap (hcOptions GHC) buildInfo))
  }
  where
    buildInfo    = allBuildInfo pkgDesc
    dir          = dropFileName file

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

cabalConfiguration :: FilePath -> GenericPackageDescription -> Either String Info
cabalConfiguration cabalFile desc =
  case finalizePackageDescription []
                                  (const True)
                                  buildPlatform
                                  buildCompiler
                                  []
                                  desc of
       Left e -> Left $ "Issue with package configuration\n" ++ show e
       Right (pkgDesc,_) -> Right $ dumpPackageDescription pkgDesc cabalFile

