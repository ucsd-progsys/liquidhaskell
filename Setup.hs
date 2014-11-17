import Control.Monad
import Data.Maybe
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.System
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process

main       = defaultMainWithHooks fixHooks
  where
  fixHooks = simpleUserHooks { postBuild = buildFixpoint
                             , postCopy = copyFixpoint
                             , postInst = copyFixpoint
                             }

copyFixpoint _ _ pkg lbi = do
  copyFile fixpoint bin
  where
  allDirs     = absoluteInstallDirs pkg lbi NoCopyDest
  bin         = bindir allDirs </> "fixpoint.native"
             ++ if system == "i686-w64-mingw32" then ".exe" else ""
  fixpoint    = "external" </> "fixpoint" </> "fixpoint.native"
             ++ if build then "" else "-" ++ system
  system      = case hostPlatform lbi of
                  Platform I386 Linux -> "i386-linux"
                  Platform X86_64 Linux -> "x86_64-linux"
                  Platform X86_64 OSX -> "x86_64-darwin"
                  Platform _      Windows -> "i686-w64-mingw32"
                  _ -> error "We don't have a prebuilt fixpoint.native for your system, please install with -fbuild-external (requires ocaml)"
  flags       = configConfigurationsFlags $ configFlags lbi
  build       = fromMaybe False $ lookup (FlagName "build-external") flags


buildFixpoint _ _ pkg lbi = when build $ do
  setEnv "Z3MEM" (show z3mem)
  executeShellCommand "./configure"
  executeShellCommand "./build.sh"
  executeShellCommand "chmod a+x external/fixpoint/fixpoint.native "
  where
  allDirs     = absoluteInstallDirs pkg lbi NoCopyDest
  binDir      = bindir allDirs ++ "/"
  flags       = configConfigurationsFlags $ configFlags lbi
  z3mem       = fromMaybe False $ lookup (FlagName "z3mem") flags
  build       = fromMaybe False $ lookup (FlagName "build-external") flags

executeShellCommand cmd   = putStrLn ("EXEC: " ++ cmd) >> system cmd >>= check
  where
    check (ExitSuccess)   = return ()
    check (ExitFailure n) = error $ "cmd: " ++ cmd ++ " failure code " ++ show n

