module Gradual.Refinements (makeGMap) where

import Gradual.Types
import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Monad
import Language.Fixpoint.Solver.Solve (solverInfo)
import Language.Fixpoint.Utils.Files 

import Control.Monad (filterM)
-- import Control.Monad.IO.Class

makeGMap :: Config -> SInfo a -> [(KVar, (GWInfo, [Expr]))] -> IO (GMap ())
makeGMap cfg sinfo mes = toGMap <$> runSolverM cfg' sI act 
  where
    sI   = solverInfo cfg' sinfo
    act  = mapM concretize mes
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

concretize :: (KVar, (GWInfo, [Expr])) -> SolveM (KVar, ((),[Expr]))
concretize (kv, (info, es))
  = (\es' -> (kv,((),es'))) <$> filterM (isGoodInstance info) es

isGoodInstance :: GWInfo -> Expr -> SolveM Bool 
isGoodInstance info e = (&&) <$> (isLocal info e) <*> (isMoreSpecific info e) 
{- 
isGoodInstance info e = do 
  l <- isLocal info e 
  s <- isMoreSpecific info e
  liftIO $ putStrLn ("Checking " ++ showFix e ++ 
            "( isLocal = " ++ show l ++ 
            "& isMoreSpecific = " ++ show s ++ ")\n"
            ) 
  return (l && s)
-}

isLocal :: GWInfo -> Expr -> SolveM Bool 
isLocal i e = isValid (PExist [(gsym i, gsort i)] e)

isMoreSpecific :: GWInfo -> Expr -> SolveM Bool
isMoreSpecific i e = isValid (e `PImp` gexpr i)


isValid :: Expr -> SolveM Bool 
isValid e = not <$> checkSat (PNot e)
{- 
isValid e = do -- not <$> checkSat (PNot e)
  r <- checkSat (PNot e)
  liftIO $ putStrLn ("CHECKING VALIDITY OF " ++ showFix e ++ " = " ++ show r)
  return $ not r  
-}
