module Language.Haskell.Liquid.FixInterface (solve, resultExit) where

{- Interfacing with Fixpoint Binary -}

import Data.Functor
import Data.List
import Data.Map hiding (map, filter) 
import Control.Monad (forM_)
import System.Directory (copyFile, removeFile)
import System.IO        (withFile, IOMode (..))
import System.Process   (system)
import System.Exit
import Text.Printf
import Outputable hiding (empty)
import Data.Data

import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.Parse         (rr)
import Language.Haskell.Liquid.Constraint    (CGInfo (..))

solve fn hqs cgi
  = {-# SCC "Solve" #-} execFq fn hqs gs (elems cm) ws qs >>= {-# SCC "exitFq" #-} exitFq fn cm 
  where cm  = fromAscList $ zipWith (\i c -> (i, c {sid = Just i})) [1..] cs 
        cs  = fixCs cgi
        ws  = fixWfs cgi
        gs  = globals cgi
        qs  = specQuals cgi

execFq fn hqs globals cs ws qs 
  = do copyFiles hqs fq
       appendFile fq qstr 
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPrintDump h d)
       ec <- {-# SCC "sysCall" #-} system $ execCmd fn 
       return ec
    where fq   = extFileName Fq  fn
          fo   = extFileName Out fn
          d    = {-# SCC "FixPointify" #-} toFixpoint (FI cs ws globals)
          qstr = showSDoc ((vcat $ toFix <$> qs) $$ blankLine)

-- execCmd fn = printf "fixpoint.native -notruekvars -refinesort -strictsortcheck -out %s %s" fo fq 
execCmd fn = printf "fixpoint.native -notruekvars -refinesort -noslice -strictsortcheck -out %s %s" fo fq 
  where fq = extFileName Fq  fn
        fo = extFileName Out fn
 
exitFq _ _ (ExitFailure n) | (n /= 1) 
  = return (Crash [] "Unknown Error", empty)
--exitFq fn cm _ 
--  = do (x, y) <- (rr . sanitizeFixpointOutput) <$> (readFile $ extFileName Out fn)
--       return  $ (plugC cm x, y) 
exitFq fn cm _ 
  = do str <- {-# SCC "readOut" #-} readFile (extFileName Out fn)
       let (x, y) = {-# SCC "parseFixOut" #-} rr ({-# SCC "sanitizeFixpointOutput" #-} sanitizeFixpointOutput str)
       return  $ (plugC cm x, y) 


sanitizeFixpointOutput 
  = unlines 
  . filter (not . ("//"     `isPrefixOf`)) 
  . chopAfter ("//QUALIFIERS" `isPrefixOf`)
  . lines

plugC _ Safe          = Safe
plugC cm (Crash is s) = Crash (mlookup cm `fmap` is) s
plugC cm (Unsafe is)  = Unsafe (mlookup cm `fmap` is)

resultExit (Crash _ _) = ExitFailure 2
resultExit (Unsafe _)  = ExitFailure 1
resultExit Safe        = ExitSuccess
