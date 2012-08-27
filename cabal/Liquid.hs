
import qualified Control.Exception as Ex
import Data.Monoid      (mconcat)
import System.Exit 

import Outputable hiding (empty) 
import Language.Haskell.Liquid.CmdLine
import Language.Haskell.Liquid.GhcInterface 
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.Constraint       
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint (FixResult (..))
import Language.Haskell.Liquid.FixInterface      
import Language.Haskell.Liquid.TransformRec   
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
  do info    <- getGhcInfo target includes :: IO GhcInfo
     donePhase "getGhcInfo"
     --putStrLn $ showPpr info 
     -- putStrLn "*************** Original CoreBinds ***************************" 
     -- putStrLn $ showPpr (cbs info)
     let cbs' = transformRecExpr (cbs info)
     donePhase "transformRecExpr"
     -- putStrLn "*************** Transform Rec Expr CoreBinds *****************" 
     -- putStrLn $ showPpr cbs'
     let cgi = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs'}
     cgi `deepseq` donePhase "generateConstraints"
     -- {-# SCC "writeCGI" #-} writeCGI target cgi
     -- donePhase "writeCGI"
     (r, sol) <- {- cgi `deepseq` -} solve target (hqFiles info) cgi
     donePhase "solve"
     {-# SCC "annotate" #-} annotate target sol $ annotMap cgi
     donePhase "annotate"
     donePhase (showPpr r) 
     -- putStrLn $ "*************** DONE: " ++ showPpr r ++ " ********************"
     return r

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
  = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi target) ({-# SCC "PPcgi" #-} showPpr cgi)
