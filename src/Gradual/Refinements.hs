module Gradual.Refinements (makeGMap) where

import Gradual.Types
import Gradual.Misc 
import Gradual.PrettyPrinting

import Language.Fixpoint.Types
-- import Language.Fixpoint.Misc (traceShow)
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Monad
import Language.Fixpoint.Solver.Solve (solverInfo)
import Language.Fixpoint.Utils.Files 
import Language.Fixpoint.SortCheck (exprSort_maybe)


import Control.Monad (filterM)
-- import Control.Monad.IO.Class

import qualified Data.List as L 

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
             (PTrue:(PAnd <$> powersetUpTo (depth cfg) es))

isGoodInstance :: GWInfo -> Expr -> SolveM Bool 
isGoodInstance info e 
  = andM [isSensible e, isLocal info e, isMoreSpecific info e]

-- isSensible is supposed to be a cheap check that checks that 
-- gradual solutions are not trivially useless 
isSensible :: Expr -> SolveM Bool 
isSensible (PIff _ (PAtom _ e1 e2))
  | e1 == e2 
  = return False 
isSensible (PAtom cmp e _)
  | cmp `elem` [Gt,Ge,Lt,Le]
  , Just s <- exprSort_maybe e 
  , boolSort == s
  = return False 
isSensible (PAnd es)  
   | length es == length (L.nub es)
   = return True 
isSensible e@(PAnd es) | 2 <= length es
  = andM $ map checkSat (e:[pAnd (ei:(PNot <$> filter (==ei) es)) | ei <- es])
isSensible _ 
  = return True 



isLocal :: GWInfo -> Expr -> SolveM Bool 
isLocal i e = do 
  let (bsE,eE) = grepIApps (gsym i) e 
  let (bsA,eA) = grepApps eE 
  let ee = PExist bsA (PExist ((gsym i, gsort i):bsE) eA)
  rr <- isValid  ee
  -- liftIO $ putStrLn ("isLocal " ++ pretty ee ++ " = " ++ show rr)
  return rr  


isMoreSpecific :: GWInfo -> Expr -> SolveM Bool
isMoreSpecific i e = do 
  let ee = (pAnd [e, gexpr i] `PImp` gexpr i)
  rr <- isValid ee 
  -- liftIO $ putStrLn ("isMoreSpecific " ++ pretty ee ++ " = " ++ show rr)
  return rr 


isValid :: Expr -> SolveM Bool
isValid e 
  | isContraPred e = return False 
  | isTautoPred  e = return True 
  | PImp (PAnd es) e2 <- e 
  , e2 `elem` es    = return True    
isValid e = not <$> checkSat (PNot e)


-------------------------------------------------------------------------------
-- | Helpers ------------------------------------------------------------------
-------------------------------------------------------------------------------

grepApps :: Expr -> ([(Symbol, Sort)], Expr)
grepApps e = (L.nub bs, e')
  where
    (bs, e') = go [] e 
    go bs (PAtom a e1 e2) = 
      let (acc1, e1') = go bs e1 in
      let (acc2, e2') = go acc1 e2 in 
      (acc2, PAtom a e1' e2')
    go bs ee@(EApp e1 e2)
      | EVar _ <- unCst e2 
      = getApp ee   
      | otherwise
      = (bs, EApp e1 e2)
    go bs (ECst e _)
      = go bs e 
    go bs (PAnd es)
      = let (bs', es') = unzip $ map (go bs) es in 
        (concat bs', PAnd es')
    go bs (POr es)
      = let (bs', es') = unzip $ map (go bs) es in 
        (concat bs', POr es')
    go bs e 
      = (bs, e)

    unCst (ECst e _) = e
    unCst e          = e  
    
    getApp e = 
     case exprSort e of 
       Just s  -> let x = symbol (pretty e) in ([(x, s)], EVar x)
       Nothing -> ([], e) 



grepIApps :: Symbol -> Expr -> ([(Symbol, Sort)], Expr)
grepIApps i e = (L.nub bs, e')
  where
    (bs, e') = go [] e 
    go bs (PAtom a e1 e2) = 
      let (acc1, e1') = go bs e1 in
      let (acc2, e2') = go acc1 e2 in 
      (acc2, PAtom a e1' e2')
    go bs ee@(EApp e1 e2)
      | unCst e2 == EVar i 
      = getApp ee   
      | otherwise
      = (bs, EApp e1 e2)
    go bs (ECst e _)
      = go bs e 
    go bs e 
      = (bs, e)

    unCst (ECst e _) = e
    unCst e          = e  
    
    getApp e = 
     case exprSort e of 
       Just s  -> let x = symbol (pretty e) in ([(x, s)], EVar x)
       Nothing -> ([], e) 


exprSort :: Expr -> Maybe Sort 
exprSort (ECst _ s) = Just s 
exprSort (EApp e _) = 
  case exprSort e of 
    Just (FFunc _ s) -> Just s
    Just s           -> Just s 
    _                -> Nothing
exprSort _ = Nothing 

