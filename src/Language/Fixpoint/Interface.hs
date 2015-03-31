module Language.Fixpoint.Interface (

    -- * Containing Constraints
    FInfo (..)

    -- * Invoke Solver on Set of Constraints
  , solve
  , solveFile

    -- * Function to determine outcome
  , resultExit

    -- * Validity Query
  , checkValid

) where

{- Interfacing with Fixpoint Binary -}

import           Data.Functor
import           Data.Hashable
import qualified Data.HashMap.Strict              as M
import           Data.List
import           Data.Monoid
import           System.Directory                 (getTemporaryDirectory)
import           System.Exit
import           System.FilePath                  ((</>))
import           System.IO                        (IOMode (..), hPutStr,
                                                   withFile)
import           Text.Printf

import           Language.Fixpoint.Config
import           Language.Fixpoint.Files
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Parse          (rr)
import           Language.Fixpoint.Types          hiding (kuts, lits)
import           System.Console.CmdArgs.Default
import           System.Console.CmdArgs.Verbosity
import           Text.PrettyPrint.HughesPJ

---------------------------------------------------------------------------
-- | One Shot validity query ----------------------------------------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
checkValid :: (Hashable a) => a -> [(Symbol, Sort)] -> Pred -> IO (FixResult a)
---------------------------------------------------------------------------
checkValid n xts p
  = do file   <- (</> show (hash n)) <$> getTemporaryDirectory
       (r, _) <- solve def file [] $ validFInfo n xts p
       return (sinfo <$> r)

validFInfo         :: a -> [(Symbol, Sort)] -> Pred -> FInfo a
validFInfo l xts p = FI constrm [] benv emptySEnv [] ksEmpty []
  where
    constrm        = M.singleton 0 $ validSubc l ibenv p
    binds          = [(x, trueSortedReft t) | (x, t) <- xts]
    ibenv          = insertsIBindEnv bids emptyIBindEnv
    (bids, benv)   = foldlMap (\e (x,t) -> insertBindEnv x t e) emptyBindEnv binds

validSubc         :: a -> IBindEnv -> Pred -> SubC a
validSubc l env p = safeHead "Interface.validSubC" $ subC env PTrue lhs rhs i t l
  where
    lhs           = mempty
    rhs           = RR mempty (predReft p)
    i             = Just 0
    t             = []

result         :: a -> Bool -> FixResult a
result _ True  = Safe
result x False = Unsafe [x]


---------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ----------------------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
solve :: Config -> FilePath -> [FilePath] -> FInfo a
      -> IO (FixResult (SubC a), M.HashMap Symbol Pred)
---------------------------------------------------------------------------
solve cfg fn hqs fi
  =   {-# SCC "Solve" #-}  execFq cfg fn hqs fi
  >>= {-# SCC "exitFq" #-} exitFq fn (cm fi)

execFq cfg fn hqs fi
  = do copyFiles hqs fq
       appendFile fq qstr
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPutStr h (render d))
       solveFile $ cfg `withTarget` fq
    where
       fq   = extFileName Fq fn
       d    = {-# SCC "FixPointify" #-} toFixpoint fi
       qstr = render ((vcat $ toFix <$> (quals fi)) $$ text "\n")

---------------------------------------------------------------------------
solveFile :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFile cfg
  = do fp  <- getFixpointPath
       z3  <- getZ3LibPath
       v   <- (\b -> if b then "-v 1" else "") <$> isLoud
       ec  <- {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ fixCommand cfg fp z3 v rf
       return ec
  where realFlags =  "-no-uif-multiply "
                  ++ "-no-uif-divide "
        rf        = if (real cfg) then realFlags else ""

fixCommand cfg fp z3 verbosity realFlags
  = printf "LD_LIBRARY_PATH=%s %s %s %s -notruekvars -refinesort -nosimple -strictsortcheck -sortedquals %s"
           z3 fp verbosity realFlags (command cfg)

exitFq _ _ (ExitFailure n) | (n /= 1)
  = return (Crash [] "Unknown Error", M.empty)
exitFq fn cm _
  = do str <- {-# SCC "readOut" #-} readFile (extFileName Out fn)
       let (x, y) = parseFixpointOutput str -- {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)
       return  $ (plugC cm x, y)

parseFixpointOutput :: String -> (FixResult Integer, FixSolution)
parseFixpointOutput str = {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)

plugC = fmap . mlookup

sanitizeFixpointOutput
  = unlines
  . filter (not . ("//"     `isPrefixOf`))
  . chopAfter ("//QUALIFIERS" `isPrefixOf`)
  . lines

resultExit Safe        = ExitSuccess
resultExit (Unsafe _)  = ExitFailure 1
resultExit _           = ExitFailure 2
