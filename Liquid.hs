{-# LANGUAGE TupleSections  #-}

import qualified Data.HashMap.Strict as M
-- import qualified Control.Exception as Ex
-- import Data.Maybe       (catMaybes)
import Data.Monoid      (mconcat, mempty)
import System.Exit 
import Control.Applicative ((<$>))
import Control.DeepSeq
import Control.Monad (when)

import CoreSyn
import Var

import System.Console.CmdArgs.Verbosity (whenLoud)
import System.Console.CmdArgs.Default
import Language.Fixpoint.Config (Config (..)) 
import Language.Fixpoint.Files
import Language.Fixpoint.Misc
import Language.Fixpoint.Interface
import Language.Fixpoint.Types (sinfo, showFix, isFalse)

import qualified Language.Haskell.Liquid.DiffCheck as DC
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.CmdLine
import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.Constraint       
import Language.Haskell.Liquid.TransformRec   

main :: IO b
main = do cfg0    <- getOpts
          res     <- mconcat <$> mapM (checkOne cfg0) (files cfg0)
          exitWith $ resultExit res

checkOne cfg0 t = getGhcInfo cfg0 t >>= either (exitWithResult cfg0 t Nothing) (liquidOne t)


liquidOne target info = 
  do donePhase Loud "Extracted Core From GHC"
     let cfg   = config $ spec info 
     whenLoud  $ do putStrLn $ showpp info 
                    putStrLn "*************** Original CoreBinds ***************************" 
                    putStrLn $ showpp (cbs info)
     let cbs' = transformScope (cbs info)
     whenLoud  $ do donePhase Loud "transformRecExpr"
                    putStrLn "*************** Transform Rec Expr CoreBinds *****************" 
                    putStrLn $ showpp cbs'
                    putStrLn "*************** Slicing Out Unchanged CoreBinds *****************" 
     dc <- prune cfg cbs' target info
     let cbs'' = maybe cbs' DC.newBinds dc
     let cgi   = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs''}
     cgi `deepseq` donePhase Loud "generateConstraints"
     -- SUPER SLOW: ONLY FOR DESPERATE DEBUGGING
     -- SUPER SLOW: whenLoud $ do donePhase Loud "START: Write CGI (can be slow!)"
     -- SUPER SLOW: {-# SCC "writeCGI" #-} writeCGI target cgi 
     -- SUPER SLOW: donePhase Loud "FINISH: Write CGI"
     (r, sol) <- solveCs cfg target cgi info
     let rNew  = checkedResult dc (result $ sinfo <$> r)
     _        <- {- when (diffcheck cfg) $ -}  DC.saveResult target rNew 
     donePhase Loud "solve"
     let out   = Just $ O (checkedNames dc) (logWarn cgi) sol (annotMap cgi)
     exitWithResult cfg target out rNew --(checkedResult dc rNew)


checkedResult dc rNew = mconcat [rOld, rNew] 
  where
     rOld             = maybe mempty DC.oldResult dc

checkedNames dc = concatMap names . DC.newBinds <$> dc
   where
     names (NonRec v _ ) = [varName v]
     names (Rec bs)      = map (varName . fst) bs

-- prune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Maybe Diff)
prune cfg cbs target info
  | not (null vs) = return . Just $ DC.DC (DC.thin cbs vs) mempty
  | diffcheck cfg = DC.slice target cbs
  | otherwise     = return Nothing
  where 
    vs            = tgtVars $ spec info


solveCs cfg target cgi info 
  = solve fx target (hqFiles info) (cgInfoFInfo cgi)
  where 
    fx = def { solver = smtsolver cfg }

writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
  where 
    str          = {-# SCC "PPcgi" #-} showpp cgi
 
