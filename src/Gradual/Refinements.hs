module Gradual.Refinements (makeGMap) where

import Gradual.Types
import Gradual.Misc 
-- import Gradual.PrettyPrinting

import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Monad
import Language.Fixpoint.Solver.Solve (solverInfo)
import Language.Fixpoint.Utils.Files 
import Language.Fixpoint.SortCheck (exprSort_maybe)


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

concretize :: GConfig -> (KVar, (GWInfo, [Expr])) -> SolveM (KVar, (GWInfo,[Expr]))
concretize cfg (kv, (info, es))
  = (\es' -> (kv,(info,es'))) <$> 
     filterM (isGoodInstance info) 
             (PTrue:(pAnd <$> powersetUpTo (depth cfg) es))

isGoodInstance :: GWInfo -> Expr -> SolveM Bool 
isGoodInstance info e 
  | isSensible e -- heuristic to delete stupit instantiations
  = (&&) <$> (isLocal info e) <*> (isMoreSpecific info e) 
  | otherwise 
  = return False 

isSensible :: Expr -> Bool 
isSensible (PIff _ (PAtom _ e1 e2))
  | e1 == e2 
  = False 
isSensible (PAtom cmp e _)
  | cmp `elem` [Gt,Ge,Lt,Le]
  , Just s <- exprSort_maybe e 
  , boolSort == s
  = False 
isSensible _ 
  = True 

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

