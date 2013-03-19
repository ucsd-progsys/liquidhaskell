import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import System.Process
import System.Exit

-- main = defaultMain

main = defaultMainWithHooks fixpointHooks

fixpointHooks  = {- autoconfUserHooks -} simpleUserHooks { postConf = buildAndCopyFixpoint } 
   
buildAndCopyFixpoint _ _ pkg lbi 
  = do putStrLn $ "POSTCONF HOOKS: " ++ show binDir -- , libDir)
       executeShellCommand "./configure"
       executeShellCommand "./build.sh"
       executeShellCommand $ "chmod a+x external/fixpoint/fixpoint.native "
       executeShellCommand $ "cp external/fixpoint/fixpoint.native " ++ binDir
       executeShellCommand $ "cp external/z3/lib/libz3.* " ++ binDir
  where 
    allDirs     = absoluteInstallDirs pkg lbi NoCopyDest
    binDir      = bindir allDirs ++ "/"
    -- libDir      = libdir allDirs

executeShellCommand cmd   = putStrLn ("EXEC: " ++ cmd) >> system cmd >>= check
  where 
    check (ExitSuccess)   = return ()
    check (ExitFailure n) = error $ "cmd: " ++ cmd ++ " failure code " ++ show n 

