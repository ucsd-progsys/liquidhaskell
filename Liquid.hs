{-# LANGUAGE BangPatterns #-}

import qualified Data.HashMap.Strict as M
import qualified Control.Exception as Ex
import Data.Monoid      (mconcat)
import System.Exit 
import Control.DeepSeq
import Control.Monad (forM)

import Language.Fixpoint.Files
import Language.Fixpoint.Names
import Language.Fixpoint.Misc
import Language.Fixpoint.Interface      
import Language.Fixpoint.Types (smtSolver, Fixpoint(..), sinfo, colorResult, FixResult (..),showFix, isFalse)

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.CmdLine
import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Constraint       
import Language.Haskell.Liquid.TransformRec   
import Language.Haskell.Liquid.Annotate (annotate)

main :: IO b
main = liquid >>= (exitWith . resultExit)

liquid  = do cfg <- getOpts
             res <- forM (files cfg) $ \t ->
                      Ex.catch (liquidOne cfg t) $ \e -> 
                      do let err = show (e :: Ex.IOException)
                         putStrLn $ "Unexpected Error: " ++ err
                         return $ Crash [] "Whoops! Unknown Failure"
             return $ mconcat res

liquidOne cfg target = 
  do _       <- getFixpointPath 
     info    <- getGhcInfo cfg target 
     donePhase Loud "getGhcInfo"
     putStrLn $ showpp info 
     putStrLn "*************** Original CoreBinds ***************************" 
     putStrLn $ showpp (cbs info)
     let cbs' = transformRecExpr (cbs info)
     donePhase Loud "transformRecExpr"
     putStrLn "*************** Transform Rec Expr CoreBinds *****************" 
     putStrLn $ showpp cbs'
     let cgi = {-# SCC "generateConstraints" #-} generateConstraints cfg $! info {cbs = cbs'}
     cgi `deepseq` donePhase Loud "generateConstraints"
     -- donePhase Loud "START: Write CGI (can be slow!)"
     -- {-# SCC "writeCGI" #-} writeCGI target cgi 
     -- donePhase Loud "FINISH: Write CGI"
     (r, sol) <- solveCs cfg target cgi info
     donePhase Loud "solve" 
     {-# SCC "annotate" #-} annotate target (resultSrcSpan r) sol $ annotMap cgi
     donePhase Loud "annotate"
     donePhase (colorResult r) (showFix r) 
     writeResult target r
     putTerminationResult $ logWarn cgi
     return r



putTerminationResult [] 
  = return ()
putTerminationResult ss 
  = do colorPhaseLn Angry "Termination Warnings:" "" 
       putStrLn $ unlines ss

solveCs cfg target cgi info 
  | nofalse cfg
  = do  hqBot <- getHqBotPath
        (_, solBot) <- solve smt target [hqBot] (cgInfoFInfoBot cgi)
        let falseKvars = M.keys (M.filterWithKey (const isFalse) solBot)
        putStrLn $ "False KVars" ++ show falseKvars
        solve smt target (hqFiles info) (cgInfoFInfoKvars cgi falseKvars)
  
  | otherwise
  = solve smt target (hqFiles info) (cgInfoFInfo cgi)
  where 
    smt = Just $ smtsolver cfg

-- getSolver cfg 
--   = case smtsolver cfg of
--       "" -> Nothing
--       x  -> Just $ smtSolver x

writeResult target = writeFile (extFileName Result target) . showFix 
resultSrcSpan      = fmap (tx . sinfo) 
  where tx (Ci x)  = x

writeCGI target cgi
  = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi target) str
  where str = {-# SCC "PPcgi" #-} showFix cgi
 

