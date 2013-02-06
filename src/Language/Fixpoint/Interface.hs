module Language.Fixpoint.Interface (
    
    -- * Containing Constraints
    FInfo (..)
 
    -- * Function to invoke solver
  , solve

    -- * Function to determine outcome
  , resultExit
  
) where

{- Interfacing with Fixpoint Binary -}

import Data.Functor
import Data.List
import qualified Data.HashMap.Strict as M
import System.IO        (withFile, IOMode (..))
import System.Exit
import Text.Printf

-- import Outputable hiding (empty)

import Language.Fixpoint.Types         hiding (kuts, lits)
import Language.Fixpoint.Misc
import Language.Fixpoint.Parse            (rr)
import Language.Fixpoint.Files
-- import Language.Haskell.Liquid.FileNames
-- import Language.Haskell.Liquid.Constraint       (CGInfo (..))

data FInfo a = FI { cm    :: M.HashMap Int (SubC a)
                  , ws    :: ![WfC a] 
                  , bs    :: !BindEnv
                  , gs    :: !FEnv
                  , lits  :: ![(Symbol, Sort)]
                  , kuts  :: Kuts 
                  , quals :: ![Qualifier]
                  }

toFixpoint x'    = kutsDoc x' $+$ gsDoc x' $+$ conDoc x' $+$ bindsDoc x' $+$ csDoc x' $+$ wsDoc x'
  where conDoc   = vcat     . map toFix_constant . lits
        csDoc    = vcat     . map toFix . cs 
        wsDoc    = vcat     . map toFix . ws 
        kutsDoc  = toFix    . kuts
        bindsDoc = toFix    . bs
        gsDoc    = toFix_gs . gs




solve fn hqs fi
  =   {-# SCC "Solve" #-}  execFq fn hqs fi
  >>= {-# SCC "exitFq" #-} exitFq fn (cm fi) 
        
execFq fn hqs fi
  = do copyFiles hqs fq
       appendFile fq qstr 
       withFile fq AppendMode (\h -> {-# SCC "HPrintDump" #-} hPrintDump h d)
       fp <- getFixpointPath
       ec <- {-# SCC "sysCall:Fixpoint" #-} executeShellCommand "fixpoint" $ execCmd fp fn 
       return ec
    where 
       fq   = extFileName Fq  fn
       d    = {-# SCC "FixPointify" #-} toFixpoint fi 
       qstr = showSDoc ((vcat $ toFix <$> (quals fi)) $$ blankLine)

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
