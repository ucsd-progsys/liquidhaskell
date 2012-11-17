{-# LANGUAGE BangPatterns #-}

import qualified Control.Exception as Ex
import Data.Monoid      (mconcat)
import System.Exit 

import Outputable hiding (empty) 
import Language.Haskell.Liquid.CmdLine
import Language.Haskell.Liquid.GhcInterface 
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.Constraint       
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint (colorResult, FixResult (..))
import Language.Haskell.Liquid.FixInterface      
import Language.Haskell.Liquid.TransformRec   
import Language.Haskell.Liquid.Annotate (annotate)
import Control.DeepSeq
import Control.Monad (forM)

main ::  IO b
main    = liquid >>= (exitWith . resultExit)

liquid  = do (targets, includes) <- getOpts
             res <- forM targets $ \t ->
                      Ex.catch (liquidOne includes t) $ \e -> 
                      do let err = show (e :: Ex.IOException)
                         putStrLn $ "Unexpected Error: " ++ err
                         return $ Crash [] "Whoops! Unknown Failure"
             return $ mconcat res

liquidOne includes target = 
  do _       <- getFixpointPath 
     info    <- getGhcInfo target includes :: IO GhcInfo
     donePhase Loud "getGhcInfo"
     -- putStrLn $ showPpr info 
     -- putStrLn "*************** Original CoreBinds ***************************" 
     -- putStrLn $ showPpr (cbs info)
     let cbs' = transformRecExpr (cbs info)
     -- donePhase Loud "transformRecExpr"
     -- putStrLn "*************** Transform Rec Expr CoreBinds *****************" 
     -- putStrLn $ showPpr cbs'
     let cgi = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs'}
     cgi `deepseq` donePhase Loud "generateConstraints"
     donePhase Loud "START: Write CGI (can be slow!)"
     {-# SCC "writeCGI" #-} writeCGI target cgi cbs'
     donePhase Loud "FINISH: Write CGI"
     (r, sol) <- solve target (hqFiles info) cgi
     donePhase Loud "solve"
     {-# SCC "annotate" #-} annotate target sol $ annotMap cgi
     donePhase Loud "annotate"
     donePhase (colorResult r) (showPpr r) 
     writeResult target r
     -- putStrLn $ "*************** DONE: " ++ showPpr r ++ " ********************"
     return r

writeResult target = writeFile (extFileName Result target) . showPpr 

{-
dummyDeepseq cgi 
  = {-# SCC "DummyWrite" #-} ( (hsCs cgi, hsWfs cgi)  `deepseq` putStrLn "DeepSeq-ed cgi")

dummyWrite target cgi
  = {-# SCC "DummyWrite" #-} (writeFile (cgiName target) ({-# SCC "PPKVARSSHOW" #-} showPpr ({-# SCC "PPKVARS" #-} kvars (hsCs cgi, hsWfs cgi) )))

dummyWrite' target cgi
  = {-# SCC "DummyWrite2" #-} (writeFile (extFileName Cgi target) ({-# SCC "PPKVARSSHOW'" #-} showPpr ({-# SCC "PPKVARS'" #-} kvars' (hsCs cgi, hsWfs cgi))))

initGhci = parseStaticFlags []
-}


writeCGI target cgi cbs 
  = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi target) str
  where str = ({-# SCC "PPcgi" #-} showSDoc (ppr cbs $+$ ppr cgi))
  








