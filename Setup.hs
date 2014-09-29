import Control.Monad
import Data.Maybe
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import System.Environment
import System.Exit
import System.Process

main         = defaultMainWithHooks fixHooks
  where
    fixHooks = simpleUserHooks { postBuild = buildFixpoint
                               , postCopy = copyFixpoint
                               , postInst = copyFixpoint
                               }

buildFixpoint _ _ pkg lbi
  = do setEnv "Z3MEM" (show z3mem)
       executeShellCommand "./configure"
       executeShellCommand "./build.sh"
       executeShellCommand "chmod a+x external/fixpoint/fixpoint.native "
  where
    allDirs     = absoluteInstallDirs pkg lbi NoCopyDest
    binDir      = bindir allDirs ++ "/"
    flags       = configConfigurationsFlags $ configFlags lbi
    z3mem       = fromMaybe False $ lookup (FlagName "z3mem") flags

copyFixpoint _ _ pkg lbi
  = do executeShellCommand $ "cp external/fixpoint/fixpoint.native " ++ binDir
       when z3mem $
         executeShellCommand $ "cp external/z3/lib/libz3.* "         ++ binDir
  where
    allDirs     = absoluteInstallDirs pkg lbi NoCopyDest
    binDir      = bindir allDirs ++ "/"
    flags       = configConfigurationsFlags $ configFlags lbi
    z3mem       = fromMaybe False $ lookup (FlagName "z3mem") flags

executeShellCommand cmd   = putStrLn ("EXEC: " ++ cmd) >> system cmd >>= check
  where
    check (ExitSuccess)   = return ()
    check (ExitFailure n) = error $ "cmd: " ++ cmd ++ " failure code " ++ show n

