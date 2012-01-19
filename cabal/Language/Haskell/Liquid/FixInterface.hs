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

import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.Parse         (rr)
import Language.Haskell.Liquid.Constraint    (CGInfo (..))

import Data.Data



--solve :: (Data a) => FilePath -> [FilePath] -> [SubC a] -> [WfC a] -> IO (FixResult (SubC a), FixSolution)

solve fn hqs cgi -- cs ws 
  = {-# SCC "Solve" #-} execFq fn hqs gs (elems cm) ws >>= exitFq fn cm 
  where cm  = fromAscList $ zipWith (\i c -> (i, c {sid = Just i})) [1..] cs 
        cs  = fixCs cgi
        ws  = fixWfs cgi
        gs  = globals cgi

execFq fn hqs globals cs ws 
  = do copyFiles  hqs fq
       withFile fq AppendMode (\h -> hPrintDump h d)
       -- ec <- system $ printf "fixpoint.native -notruekvars -noslice -strictsortcheck -out %s %s" fo fq 
       ec <- system $ printf "fixpoint.native -notruekvars -refinesort -noslice -strictsortcheck -out %s %s" fo fq 
       return (ec, su)
    where fq      = extFileName Fq  fn
          fo      = extFileName Out fn
          (d, su) = {-# SCC "toFixpoint" #-} toFixpoint (FI cs ws globals)

exitFq _ _ (ExitFailure n, _) | (n /= 1) 
  = return (Crash, empty)
exitFq fn cm (_, su) 
  = do (x, y) <- (rr . sanitizeFixpointOutput) <$> (readFile $ extFileName Out fn)
       return  $ (plugC cm x, subst su y) 

sanitizeFixpointOutput 
  = unlines 
  . filter (not . ("//"     `isPrefixOf`)) 
  . chopAfter ("//QUALIFIERS" `isPrefixOf`)
  . lines

plugC _ Safe         = Safe
plugC _ Crash        = Crash  
plugC cm (Unsafe is) = Unsafe $ map (mlookup cm) is

resultExit Crash     = ExitFailure 2
resultExit (Unsafe _)= ExitFailure 1
resultExit Safe      = ExitSuccess
