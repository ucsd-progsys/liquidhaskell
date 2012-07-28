
import GHC              --(parseStaticFlags)
import qualified Control.Exception as Ex
import Data.List        (isInfixOf)
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
import Language.Haskell.Liquid.Predicates      
import Language.Haskell.Liquid.TransformRec   
import Control.DeepSeq
import Control.Monad (forM)
import CoreSyn

-- import System.Console.CmdArgs


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
     putStrLn $ "*************** Original CoreBinds ***************************" 
     putStrLn $ showPpr (cbs info)
     let cbs' = transformRecExpr (cbs info)
     -- putStrLn $ "*************** Transform Rec Expr CoreBinds *****************" 
     -- putStrLn $ showPpr (cbs')
     let cgi = generateConstraints $ info {cbs = cbs'}
     writeConstraints target cgi
     (r, sol) <- cgi `deepseq` solve target (hqFiles info) cgi
     annotate target sol $ annotMap cgi
     putStrLn $ "*************** DONE: " ++ showPpr r ++ " ********************"
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


writeConstraints target cgi 
  = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi target) ({-# SCC "PPcgi" #-} showPpr cgi)
