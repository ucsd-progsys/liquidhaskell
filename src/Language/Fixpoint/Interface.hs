module Language.Fixpoint.Interface (solve, resultExit) where

{- Interfacing with Fixpoint Binary -}

import Data.Functor
import Data.List
import qualified Data.HashMap.Strict as M
import System.IO        (withFile, IOMode (..))
import System.Exit
import Text.Printf
import Outputable hiding (empty)

import Language.Haskell.Liquid.Fixpoint         hiding (kuts, lits)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.Parse            (rr)
import Language.Haskell.Liquid.Constraint       (CGInfo (..))

solve fn hqs cgi
  =     {-# SCC "Solve" #-}  execFq fn hqs qs fi
    >>= {-# SCC "exitFq" #-} exitFq fn cm 
  where fi  = FI (M.elems cm) (fixWfs cgi) (binds cgi) (globals cgi) (lits cgi) (kuts cgi)  
        cm  = M.fromList $ addIds $ fixCs cgi 
        qs  = specQuals cgi
        
execFq fn hqs qs fi -- globals cs ws ks 
  = do copyFiles hqs fq
       appendFile fq qstr 
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPrintDump h d)
       fp <- getFixpointPath
       ec <- {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ execCmd fp fn 
       return ec
    where fq   = extFileName Fq  fn
          d    = {-# SCC "FixPointify" #-} toFixpoint fi 
          qstr = showSDoc ((vcat $ toFix <$> qs) $$ blankLine)

-- execCmd fn = printf "fixpoint.native -notruekvars -refinesort -strictsortcheck -out %s %s" fo fq 
execCmd fp fn = printf "%s -notruekvars -refinesort -noslice -nosimple -strictsortcheck -sortedquals -out %s %s" fp fo fq 
  where fq    = extFileName Fq  fn
        fo    = extFileName Out fn

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
