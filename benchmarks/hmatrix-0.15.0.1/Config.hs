{-
    GSL and LAPACK may require auxiliary libraries which depend on OS,
    distribution, and implementation. This script tries to to find out
    the correct link command for your system.
    Suggestions and contributions are welcome.

    By default we try to link -lgsl -llapack. This works in ubuntu/debian,
    both with and without ATLAS.
    If this fails we try different sets of additional libraries which are
    known to work in some systems.

    The desired libraries can also be explicitly given by the user using cabal
    flags (e.g., -fmkl, -faccelerate) or --configure-option=link:lib1,lib2,lib3,...

-}

module Config(config) where

import System.Process
import System.Exit
import System.Environment
import System.Directory(createDirectoryIfMissing)
import System.FilePath((</>))
import Data.List(isPrefixOf, intercalate)
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Configure
import Distribution.PackageDescription

-- possible additional dependencies for the desired libs (by default gsl lapack)

opts = [ ""                              -- Ubuntu/Debian
       , "blas"
       , "blas cblas"
       , "cblas"
       , "gslcblas"
       , "blas gslcblas"
       , "f77blas"
       , "f77blas cblas atlas gcc_s"     -- Arch Linux (older version of atlas-lapack)
       , "blas gslcblas gfortran"        -- Arch Linux with normal blas and lapack
       ]

-- location of test program
testProgLoc bInfo = buildDir bInfo </> "dummy.c"
testOutLoc bInfo = buildDir bInfo </> "dummy"

-- write test program
writeTestProg bInfo contents = writeFile (testProgLoc bInfo) contents

-- compile, discarding error messages
compile cmd = do
    let processRecord = (shell $ join cmd) { std_out = CreatePipe
                                           , std_err = CreatePipe }
    ( _, _, _, h) <- createProcess processRecord
    waitForProcess h

-- command to compile the test program
compileCmd bInfo buildInfo = [ "gcc "
                             , (join $ ccOptions buildInfo)  
                             , (join $ cppOptions buildInfo) 
                             , (join $ map ("-I"++) $ includeDirs buildInfo) 
                             , testProgLoc bInfo
                             , "-o"
                             , testOutLoc bInfo 
                             , (join $ map ("-L"++) $ extraLibDirs buildInfo) 
                             ]
 
-- compile a simple program with symbols from GSL and LAPACK with the given libs
testprog bInfo buildInfo libs fmks = do
    writeTestProg bInfo "#include <gsl/gsl_sf_gamma.h>\nint main(){dgemm_(); zgesvd_(); gsl_sf_gamma(5);}"
    compile $ compileCmd bInfo 
                         buildInfo 
                            ++ [ (prepend "-l" $ libs)
                               , (prepend "-framework " fmks) ] 

join = intercalate " "
prepend x = unwords . map (x++) . words

check bInfo buildInfo libs fmks = (ExitSuccess ==) `fmap` testprog bInfo buildInfo libs fmks

-- simple test for GSL
gsl bInfo buildInfo = do
    writeTestProg bInfo "#include <gsl/gsl_sf_gamma.h>\nint main(){gsl_sf_gamma(5);}"
    compile $ compileCmd bInfo buildInfo ++ ["-lgsl", "-lgslcblas"]

-- test for gsl >= 1.12
gsl112 bInfo buildInfo = do
    writeTestProg bInfo "#include <gsl/gsl_sf_exp.h>\nint main(){gsl_sf_exprel_n_CF_e(1,1,0);}"
    compile $ compileCmd bInfo buildInfo ++ ["-lgsl", "-lgslcblas"]

-- test for odeiv2
gslodeiv2 bInfo buildInfo = do
    writeTestProg bInfo "#include <gsl/gsl_odeiv2.h>\nint main(){return 0;}"
    compile $ compileCmd bInfo buildInfo ++ ["-lgsl", "-lgslcblas"]

checkCommand c = (ExitSuccess ==) `fmap` c

-- test different configurations until the first one works
try _ _ _ _ [] = return Nothing
try l i b f (opt:rest) = do
    ok <- check l i (b ++ " " ++ opt) f
    if ok then return (Just opt)
          else try l i b f rest

-- read --configure-option=link:lib1,lib2,lib3,etc
linkop = "--configure-option=link:"
getUserLink = concatMap (g . drop (length linkop)) . filter (isPrefixOf linkop)
    where g = map cs
          cs ',' = ' '
          cs x   = x

config :: LocalBuildInfo -> IO HookedBuildInfo
          
config bInfo = do
    putStr "Checking foreign libraries..."
    args <- getArgs

    let Just lib = library . localPkgDescr $ bInfo
        buildInfo = libBuildInfo lib
        base = unwords . extraLibs $ buildInfo
        fwks = unwords . frameworks $ buildInfo
        auxpref = getUserLink args

    -- We extract the desired libs from hmatrix.cabal (using a cabal flags)
    -- and from a posible --configure-option=link:lib1,lib2,lib3
    -- by default the desired libs are gsl lapack.

    let pref = if null (words (base ++ " " ++ auxpref)) then "gsl lapack" else auxpref
        fullOpts = map ((pref++" ")++) opts

    -- create the build directory (used for tmp files) if necessary
    createDirectoryIfMissing True $ buildDir bInfo
    
    r <- try bInfo buildInfo base fwks fullOpts

    case r of
        Nothing -> do
            putStrLn " FAIL"
            g  <- checkCommand $ gsl bInfo buildInfo
            if g
                then putStrLn " *** Sorry, I can't link LAPACK."
                else putStrLn " *** Sorry, I can't link GSL."
            putStrLn " *** Please make sure that the appropriate -dev packages are installed."
            putStrLn " *** You can also specify the required libraries using"
            putStrLn " *** cabal install hmatrix --configure-option=link:lib1,lib2,lib3,etc."            
            return (Just emptyBuildInfo { buildable = False }, [])
        Just ops -> do
            putStrLn $ " OK " ++ ops
            g1 <- checkCommand $ gsl112 bInfo buildInfo
            let op1 = if g1 then "" else "-DGSL110"
            g2 <- checkCommand $ gslodeiv2 bInfo buildInfo
            let op2 = if g2 then "" else "-DGSLODE1"
                opts = filter (not.null) [op1,op2]
            let hbi = emptyBuildInfo { extraLibs = words ops, ccOptions = opts }
            return (Just hbi, [])

