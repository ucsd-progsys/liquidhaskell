module Language.Fixpoint.Interface (
    
    -- * Containing Constraints
    FInfo (..)
 
    -- * Function to invoke solver
  , solve, solveFile

    -- * Function to determine outcome
  , resultExit
  
) where

{- Interfacing with Fixpoint Binary -}

import Data.Functor
import Data.List
import qualified Data.HashMap.Strict as M
import System.IO        (hPutStr, withFile, IOMode (..))
import System.Exit
import Text.Printf

import Language.Fixpoint.Types         hiding (kuts, lits)
import Language.Fixpoint.Misc
import Language.Fixpoint.Parse            (rr)
import Language.Fixpoint.Files
import Text.PrettyPrint.HughesPJ

solve fn hqs fi
  =   {-# SCC "Solve" #-}  execFq fn hqs fi
  >>= {-# SCC "exitFq" #-} exitFq fn (cm fi) 
 
      
execFq fn hqs fi
  = do copyFiles hqs fq
       appendFile fq qstr 
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPutStr h (render d))
       solveFile fq fo
    where 
       fq   = extFileName Fq  fn
       fo   = extFileName Out fn
       d    = {-# SCC "FixPointify" #-} toFixpoint fi 
       qstr = render ((vcat $ toFix <$> (quals fi)) $$ text "\n")


solveFile fq fo 
  = do fp <- getFixpointPath
       z3 <- getZ3LibPath
       ec <- {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ fixCommand fp z3 fq fo  
       return ec
 
-- execCmd fn = printf "fixpoint.native -notruekvars -refinesort -strictsortcheck -out %s %s" fo fq 
fixCommand fp z3 fin fout 
  = printf "LD_LIBRARY_PATH=%s %s -notruekvars -refinesort -noslice -nosimple -strictsortcheck -sortedquals -out %s %s" 
           z3 fp fout fin


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
