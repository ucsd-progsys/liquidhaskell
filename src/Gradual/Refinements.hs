module Gradual.Refinements (makeGMap) where

import Gradual.Types
import Gradual.Misc 
-- import Gradual.PrettyPrinting

import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Monad
import Language.Fixpoint.Solver.Solve (solverInfo)
import Language.Fixpoint.Utils.Files 

import Control.Monad (filterM)
-- import Control.Monad.IO.Class

makeGMap :: GConfig -> Config -> SInfo a -> [(KVar, (GWInfo, [Expr]))] -> IO (GMap GWInfo)
makeGMap gcfg cfg sinfo mes = toGMap <$> runSolverM cfg' sI act 
  where
    sI   = solverInfo cfg' sinfo
    act  = mapM (concretize gcfg) mes
    cfg' = cfg { srcFile        = srcFile cfg `withExt` Pred 
               , extensionality = True -- disable mbqi
           }

{-
makeGMap cfg sinfo mes = do 
  putStrLn "MakeGMap: \n\n"
  putStrLn (concatMap (\(k,(_,es)) -> (show k ++ " |-> " ++ showFix es ++"\n\n")) mes)
  mes' <- runSolverM cfg sI $ mapM concretize mes
  putStrLn (concatMap (\(k,(_,es)) -> (show k ++ " |-> " ++ showFix es ++"\n\n")) mes')
  return $ toGMap mes' 
  where
    sI = solverInfo cfg sinfo
-}

concretize :: GConfig -> (KVar, (GWInfo, [Expr])) -> SolveM (KVar, (GWInfo,[Expr]))
concretize cfg (kv, (info, es))
  = (\es' -> (kv,(info,es'))) <$> 
     filterM (isGoodInstance info) 
             (PTrue:(pAnd <$> powersetUpTo (depth cfg) es))

isGoodInstance :: GWInfo -> Expr -> SolveM Bool 
isGoodInstance info e = (&&) <$> (isLocal info e) <*> (isMoreSpecific info e) 

{- 
isGoodInstance info e = do 
  l <- isLocal info e 
  s <- isMoreSpecific info e
  liftIO $ putStrLn ("Checking " ++ pretty e ++ 
            ":: (isLocal = " ++ show l ++ 
            " & isMoreSpecific than (" ++ pretty (gexpr info) ++ ") = " ++ show s ++ ")\n"
            ) 
  return (l && s)
-}

isLocal :: GWInfo -> Expr -> SolveM Bool 
isLocal i e = isValid (PExist [(gsym i, gsort i)] e)

isMoreSpecific :: GWInfo -> Expr -> SolveM Bool
isMoreSpecific i e = isValid (pAnd [e, gexpr i] `PImp` gexpr i)


isValid :: Expr -> SolveM Bool
isValid e 
  | isContraPred e = return False 
  | isTautoPred  e = return True 
  | PImp (PAnd es) e2 <- e 
  , e2 `elem` es    = return True    
isValid e = not <$> checkSat (PNot e)

{- 
isValid e = do -- not <$> checkSat (PNot e)
  r <- checkSat (PNot e)
  liftIO $ putStrLn ("CHECKING VALIDITY OF " ++ showFix e ++ " = " ++ show r)
  return $ not r  
-}
