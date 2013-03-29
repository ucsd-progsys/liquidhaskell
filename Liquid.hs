{-# LANGUAGE BangPatterns #-}

import qualified Data.HashMap.Strict as M
import qualified Control.Exception as Ex
import Data.Monoid      (mconcat)
import System.Exit 
import Control.DeepSeq
import Control.Monad (forM)


import Outputable hiding (empty) 

import Language.Fixpoint.Files
import Language.Fixpoint.Names
import Language.Fixpoint.Misc
import Language.Fixpoint.Interface      
import Language.Fixpoint.Types (Fixpoint(..), sinfo, colorResult, FixResult (..),showFix, isFalse)

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.CmdLine
import Language.Haskell.Liquid.GhcInterface 
import Language.Haskell.Liquid.Constraint       
import Language.Haskell.Liquid.TransformRec   
import Language.Haskell.Liquid.Annotate (annotate)

main ::  IO b
main    = liquid >>= (exitWith . resultExit)

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
     putStrLn $ showFix info 
     putStrLn "*************** Original CoreBinds ***************************" 
     putStrLn $ showPpr (cbs info)
     let cbs' = transformRecExpr (cbs info)
     donePhase Loud "transformRecExpr"
     putStrLn "*************** Transform Rec Expr CoreBinds *****************" 
     putStrLn $ showPpr cbs'
     let cgi = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs'}
     cgi `deepseq` donePhase Loud "generateConstraints"
     -- donePhase Loud "START: Write CGI (can be slow!)"
     -- {-# SCC "writeCGI" #-} writeCGI target cgi 
     -- donePhase Loud "FINISH: Write CGI"
     hqBot <- getHqBotPath
     (_, solBot) <- solve target [hqBot] (cgInfoFInfoBot cgi)
     let falseKvars = M.keys (M.filterWithKey (const isFalse) solBot)
     putStrLn $ "False KVars" ++ show falseKvars
     (r, sol)    <- solve target (hqFiles info) (cgInfoFInfo cgi falseKvars)
     donePhase Loud "solve"
     {-# SCC "annotate" #-} annotate target (resultSrcSpan r) sol $ annotMap cgi
     donePhase Loud "annotate"
     donePhase (colorResult r) (showFix r) 
     writeResult target r
     -- putStrLn $ "*************** DONE: " ++ showPpr r ++ " ********************"
     return r

writeResult target = writeFile (extFileName Result target) . showFix
resultSrcSpan      = fmap (tx . sinfo) 
  where tx (Ci x)  = x
{-
dummyDeepseq cgi 
  = {-# SCC "DummyWrite" #-} ( (hsCs cgi, hsWfs cgi)  `deepseq` putStrLn "DeepSeq-ed cgi")

dummyWrite target cgi
  = {-# SCC "DummyWrite" #-} (writeFile (cgiName target) ({-# SCC "PPKVARSSHOW" #-} showPpr ({-# SCC "PPKVARS" #-} kvars (hsCs cgi, hsWfs cgi) )))

dummyWrite' target cgi
  = {-# SCC "DummyWrite2" #-} (writeFile (extFileName Cgi target) ({-# SCC "PPKVARSSHOW'" #-} showPpr ({-# SCC "PPKVARS'" #-} kvars' (hsCs cgi, hsWfs cgi))))

initGhci = parseStaticFlags []
-}


writeCGI target cgi
  = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi target) str
  where str = {-# SCC "PPcgi" #-} showFix cgi
 

