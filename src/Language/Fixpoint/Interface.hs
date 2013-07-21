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

import Data.Hashable
import Data.Monoid
import Data.Functor
import Data.List
import qualified Data.HashMap.Strict as M
import System.IO        (hPutStr, withFile, IOMode (..))
import System.Exit
import System.Directory (getTemporaryDirectory)
import System.FilePath  ((</>))
import Text.Printf

import Language.Fixpoint.Config
import Language.Fixpoint.Types         hiding (kuts, lits)
import Language.Fixpoint.Misc
import Language.Fixpoint.Parse            (rr)
import Language.Fixpoint.Files
import Text.PrettyPrint.HughesPJ
import System.Console.CmdArgs.Default

---------------------------------------------------------------------------
-- | One Shot validity query ----------------------------------------------
---------------------------------------------------------------------------

checkValid :: (Hashable a) => a -> [(Symbol, Sort)] -> Pred -> IO (FixResult a) 
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
validSubc l env p = subC env PTrue lhs rhs i t l
  where 
    lhs           = top
    rhs           = RR mempty (predReft p)
    i             = Just 0
    t             = []

result         :: a -> Bool -> FixResult a    
result _ True  = Safe 
result x False = Unsafe [x]


---------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ----------------------------
---------------------------------------------------------------------------

solve :: Config -> FilePath -> [FilePath] -> FInfo a -> IO (FixResult (SubC a), M.HashMap Symbol Pred)
solve smt fn hqs fi
  =   {-# SCC "Solve" #-}  execFq smt fn hqs fi
  >>= {-# SCC "exitFq" #-} exitFq fn (cm fi) 
      
execFq smt fn hqs fi
  = do copyFiles hqs fq
       appendFile fq qstr 
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPutStr h (render d))
       solveFile $ def { inFile = fq } { outFile = fo }
    where 
       fq   = extFileName Fq  fn
       fo   = extFileName Out fn
       d    = {-# SCC "FixPointify" #-} toFixpoint fi 
       qstr = render ((vcat $ toFix <$> (quals fi)) $$ text "\n")

solveFile :: Config -> IO ExitCode 
solveFile cfg -- fq fo 
  = do fp <- getFixpointPath
       z3 <- getZ3LibPath
       ec <- {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ fixCommand cfg fp z3 -- fq fo  
       return ec
 
-- execCmd fn = printf "fixpoint.native -notruekvars -refinesort -strictsortcheck -out %s %s" fo fq 
fixCommand cfg fp z3 -- fin fout 
  = printf "LD_LIBRARY_PATH=%s %s %s -notruekvars -refinesort -noslice -nosimple -strictsortcheck -sortedquals" 
           z3 fp (show cfg) -- fout fin

exitFq _ _ (ExitFailure n) | (n /= 1) 
  = return (Crash [] "Unknown Error", M.empty)
exitFq fn cm _ 
  = do str <- {-# SCC "readOut" #-} readFile (extFileName Out fn)
       let (x, y) = {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)
       return  $ (plugC cm x, y) 

plugC = fmap . mlookup

sanitizeFixpointOutput 
  = unlines 
  . filter (not . ("//"     `isPrefixOf`)) 
  . chopAfter ("//QUALIFIERS" `isPrefixOf`)
  . lines

resultExit Safe        = ExitSuccess
resultExit (Unsafe _)  = ExitFailure 1
resultExit _           = ExitFailure 2

