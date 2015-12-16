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

module Language.Haskell.Liquid.Cabal (cabalInfo, Info(..)) where

import Control.Exception
import Data.Bits                              ( shiftL, shiftR, xor )
import Data.Char                              ( ord, isSpace )
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Word ( Word32 )
import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Configuration
import Distribution.PackageDescription.Parse
import Distribution.Simple.BuildPaths
import Distribution.System
import Distribution.Verbosity
import Language.Haskell.Extension
import Numeric ( showHex )
import System.Console.CmdArgs
import System.Environment
import System.Exit
import System.FilePath
import System.Directory
import System.Info
import System.Process

import Language.Haskell.Liquid.Errors

-----------------------------------------------------------------------------------------------
cabalInfo :: FilePath -> IO (Maybe Info)
-----------------------------------------------------------------------------------------------
cabalInfo tgt = do
  f    <- canonicalizePath tgt
  mbCf <- findCabalFile f
  case mbCf of
    Just cf -> Just  <$> processCabalFile cf
    Nothing -> return Nothing

processCabalFile :: FilePath -> IO Info
processCabalFile cf = do
  distDir <- distDirectory cf
  i       <- cabalConfiguration cf distDir <$> readPackageDescription silent cf
  i       <- addPackageDbs =<< canonicalizePaths i
  whenLoud $ putStrLn $ "Cabal Info: " ++ show i
  return i


--------------------------------------------------------------------------------
distDirectory :: FilePath -> IO FilePath
--------------------------------------------------------------------------------
distDirectory cf = do
  d1    <- sandboxDistDir cf
  d2    <- stackDistDir   cf
  d3    <- defaultDistDir cf
  return $ firstJust d3 [d1, d2]

firstJust :: a -> [Maybe a] -> a
firstJust d []             = d
firstJust _ (Just x  : _)  = x
firstJust d (Nothing : xs) = firstJust d xs

sandboxDistDir :: FilePath -> IO (Maybe FilePath)
sandboxDistDir f = do
  let sandboxDir = sandboxBuildDir (takeDirectory f </> ".cabal-sandbox")
  b <- doesDirectoryExist sandboxDir
  return $ if b then Just sandboxDir else Nothing

defaultDistDir :: FilePath -> IO FilePath
defaultDistDir _ = return "dist"

stackDistDir :: FilePath -> IO (Maybe FilePath)
stackDistDir cf = (splice <$>) <$> execInPath cmd cf
  where
    cmd         = "stack path --dist-dir"
    splice      = (takeDirectory cf </>) . trim

--------------------------------------------------------------------------------
getStackDbs :: FilePath -> IO [FilePath]
--------------------------------------------------------------------------------
getStackDbs p = do mpp <- execInPath cmd p
                   case mpp of
                     Just pp -> extractDbs pp
                     Nothing -> return []
  where
        cmd   = "stack --verbosity quiet exec printenv GHC_PACKAGE_PATH"

extractDbs :: String -> IO [FilePath]
extractDbs = filterM doesDirectoryExist . stringPaths

filterM f (x:xs) = do b  <- f x
                      ys <- filterM f xs
                      return $ if b then (x : ys) else ys
filterM f []     = return []

stringPaths :: String -> [String]
stringPaths = splitBy ':' . trim

splitBy :: Char -> String -> [String]
splitBy c str
  | null str' = [x]
  | otherwise = x : splitBy c (tail str')
  where
    (x, str') = span (c /=) str

execInPath :: String -> FilePath -> IO (Maybe String)
execInPath cmd p = do
  eIOEstr <- try $ readCreateProcess prc "" :: IO (Either IOError String)
  return $ case eIOEstr of
            Right s -> Just s
            -- This error is most likely "/bin/sh: stack: command not found"
            -- which is caused by the package containing a stack.yaml file but
            -- no stack command is in the PATH.
            Left _  -> Nothing
      where
        prc          = (shell cmd) { cwd = Just $ takeDirectory p }

trim :: String -> String
trim = f . f
  where
   f = reverse . dropWhile isSpace

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
findInDir p d = do
  files <- getDirectoryContents d
  return [ d </> f | f <- files, p f ]

-----------------------------------------------------------------------------------------------

-- INVARIANT: all FilePaths must be absolute
data Info = Info { cabalFile    :: FilePath
                 , buildDirs    :: [FilePath]
                 , sourceDirs   :: [FilePath]
                 , exts         :: [Extension]
                 , otherOptions :: [String]
                 , packageDbs   :: [String]
                 , packageDeps  :: [String]
                 , macroPath    :: FilePath
                 } deriving (Show)

addPackageDbs :: Info -> IO Info
addPackageDbs i = do
  boxDbs <- getSandboxDbs i
  stkDbs <- getStackDbs (dir i)
  return  $ i { packageDbs = stkDbs ++ boxDbs ++ packageDbs i}

getSandboxDbs :: Info -> IO [FilePath]
getSandboxDbs i = do
  tM <- maybeReadFile $ sandBoxFile i
  case tM of
   Just t  -> return [T.unpack $ parsePackageDb t]
   Nothing -> return []

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
sandBoxFile i = dir i </> "cabal.sandbox.config"

dir :: Info -> FilePath
dir = takeDirectory . cabalFile

dumpPackageDescription :: PackageDescription -> FilePath -> FilePath -> Info
dumpPackageDescription pkgDesc file distDir = Info {
    cabalFile    = file
  , buildDirs    = nub (map normalise buildDirs)
  , sourceDirs   = nub (normalise <$> getSourceDirectories buildInfo dir)
  , exts         = nub (concatMap usedExtensions buildInfo)
  , otherOptions = nub (filter isAllowedOption (concatMap (hcOptions GHC) buildInfo))
  , packageDbs   = []
  , packageDeps  = nub [ unPackName n | Dependency n _ <- buildDepends pkgDesc, n /= thisPackage ]
  , macroPath    = macroPath
  }
  where
    (buildDirs, macroPath) = getBuildDirectories pkgDesc distDir
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

getBuildDirectories :: PackageDescription -> FilePath -> ([String], FilePath)
getBuildDirectories pkgDesc distDir =
  ( case library pkgDesc of
      Just _  -> buildDir : buildDirs
      Nothing -> buildDirs
  , autogenDir </> cppHeaderName)
  where
    buildDir       = distDir </> "build"
    autogenDir     = buildDir </> "autogen"
    execBuildDir e = buildDir </> exeName e </> (exeName e ++ "-tmp")
    buildDirs      = autogenDir : map execBuildDir (executables pkgDesc)


-- See https://github.com/haskell/cabal/blob/master/cabal-install/Distribution/Client/Sandbox.hs#L137-L158
sandboxBuildDir :: FilePath -> FilePath
sandboxBuildDir sandboxDir = "dist/dist-sandbox-" ++ showHex sandboxDirHash ""
  where
    sandboxDirHash = jenkins sandboxDir

    -- See http://en.wikipedia.org/wiki/Jenkins_hash_function
    jenkins :: String -> Word32
    jenkins str = loop_finish $ foldl' loop 0 str
      where
        loop :: Word32 -> Char -> Word32
        loop hash key_i' = hash'''
          where
            key_i   = toEnum . ord $ key_i'
            hash'   = hash + key_i
            hash''  = hash' + (shiftL hash' 10)
            hash''' = hash'' `xor` (shiftR hash'' 6)

        loop_finish :: Word32 -> Word32
        loop_finish hash = hash'''
          where
            hash'   = hash + (shiftL hash 3)
            hash''  = hash' `xor` (shiftR hash' 11)
            hash''' = hash'' + (shiftL hash'' 15)

isAllowedOption :: String -> Bool
isAllowedOption opt = elem opt allowedOptions || any (`isPrefixOf` opt) allowedOptionPrefixes

buildCompiler :: CompilerId
buildCompiler = CompilerId buildCompilerFlavor compilerVersion

cabalConfiguration :: FilePath -> FilePath -> GenericPackageDescription -> Info
cabalConfiguration cabalFile distDir desc =
  case finalizePackageDescription []
                                  (const True)
                                  buildPlatform
                                  (unknownCompilerInfo buildCompiler NoAbiTag)
                                  []
                                  desc of
       Right (pkgDesc,_) -> dumpPackageDescription pkgDesc cabalFile distDir
       Left e -> exitWithPanic $ "Issue with package configuration\n" ++ show e

canonicalizePaths :: Info -> IO Info
canonicalizePaths i = do
  buildDirs <- mapM canonicalizePath (buildDirs i)
  macroPath <- canonicalizePath (macroPath i)
  return (i { buildDirs = buildDirs, macroPath = macroPath })

{-
  Cabal Info: Info {cabalFile = "/Users/rjhala/research/stack/liquid/liquidhaskell/liquidhaskell.cabal",
  buildDirs = ["/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build",
               "/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen",
               "/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/liquid/liquid-tmp",
               "/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/lhi/lhi-tmp"],
  sourceDirs = ["/Users/rjhala/research/stack/liquid/liquidhaskell/src",
                "/Users/rjhala/research/stack/liquid/liquidhaskell/include",
                "/Users/rjhala/research/stack/liquid/liquidhaskell/"],
  exts = [EnableExtension PatternGuards],

  otherOptions = ["-W","-fno-warn-unused-imports","-fno-warn-dodgy-imports","-fno-warn-deprecated-flags","-fno-warn-deprecations","-fno-warn-missing-methods"],

  packageDbs = ["/Users/rjhala/research/stack/liquid/.stack-work/install/x86_64-osx/nightly-2015-09-24/7.10.2/pkgdb",
                "/Users/rjhala/.stack/snapshots/x86_64-osx/nightly-2015-09-24/7.10.2/pkgdb",
                "/Applications/ghc-7.10.2.app/Contents/lib/ghc-7.10.2/package.conf.d"],

  packageDeps = ["Cabal","Diff","aeson","array","base","bifunctors","bytestring","cereal","cmdargs","containers","cpphs","daemons","data-default","deepseq","directory","filepath","fingertree","ghc","ghc-paths","hashable","hpc","hscolour","liquid-fixpoint","mtl","network","parsec","pretty","process","prover","syb","template-haskell","text","time","unix","unordered-containers","vector"], macroPath = "/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen/cabal_macros.h"}
-}
