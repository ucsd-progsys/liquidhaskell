import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import System.Process
import System.Exit

-- main = defaultMain

main = defaultMainWithHooks fixpointHooks

fixpointHooks  = {- simpleUserHooks -} autoconfUserHooks { postConf = buildAndCopyFixpoint } 
   
buildAndCopyFixpoint _ _ pkg lbi 
  = do putStrLn $ "POSTCONF HOOKS: " ++ show (binDir, libDir)
       executeShellCommand "./build.sh"
  where 
    allDirs     = absoluteInstallDirs pkg lbi NoCopyDest
    binDir      = bindir allDirs
    libDir      = libdir allDirs

executeShellCommand cmd           =   putStrLn ("EXEC: " ++ cmd) 
                                  >>  system cmd 
                                  >>= checkExitCode cmd

checkExitCode _   (ExitSuccess)   = return ()
checkExitCode cmd (ExitFailure n) = error $ "cmd: " ++ cmd ++ " failure code " ++ show n 

