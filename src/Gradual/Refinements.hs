module Gradual.Refinements (makeGMap) where

import Gradual.Log 
import Gradual.Types
import Gradual.Misc 
import Gradual.PrettyPrinting

import Language.Fixpoint.Types hiding (isNumeric)
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Monad
import Language.Fixpoint.Solver.Solve (solverInfo)
import Language.Fixpoint.Utils.Files 


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
concretize cfg (kv, (info', es)) = do 
  let cands = fmap (`subst1` (gsym info', ECst (EVar (gsym info')) (gsort info')))
                   (PAnd <$> powersetUpTo (depth cfg) es)
  let info = info' {gexpr = gexpr info' `subst1` (gsym info, ECst (EVar (gsym info)) (gsort info))}
  whenLog cfg $ logCand  kv (PTrue:(PAnd <$> powersetUpTo (depth cfg) es))
  sens  <- filterM (isSensible info) cands
  whenLog cfg $ logSens  kv (PTrue:sens)
  local <- filterM (isLocal info) sens
  whenLog cfg $ logLocal kv (PTrue:local)
  spec  <- filterM (isMoreSpecific info) (PTrue:local)
  whenLog cfg $ logSpec  kv spec
  return (kv,(info,spec))
             

_isGoodInstance :: GWInfo -> Expr -> SolveM Bool 
_isGoodInstance info e 
  = andM [isSensible info e, isLocal info e, isMoreSpecific info e]

-- isSensible is supposed to be a cheap check that checks that 
-- gradual solutions are not trivially useless 
isSensible :: GWInfo -> Expr -> SolveM Bool 
isSensible i e@(PAnd _) 
   | not ((gsym i) `elem` (syms e))
   = return False 
isSensible _ ee
  | (PIff _ (PAtom _ e1 e2)) <- unPAnd ee  
  , e1 == e2 
  = return False 
isSensible _ ee
  | PAtom cmp e _ <- unPAnd ee 
  , cmp `elem` [Gt,Ge,Lt,Le]
  , Just s <- exprSort e 
  , not (isNumeric s)
  = return False 
isSensible _ ee
  | PAtom _ e _ <- unPAnd ee 
  , Just s <- exprSort e
  , isList s
  = return False 
isSensible _ (PAnd es)  
   | length es /= length (L.nub es)
   = return False 
isSensible _ e@(PAnd _) | applyName `elem` syms e 
   = return True  
isSensible _ e@(PAnd es) | 2 <= length es
  = andM $ map checkSat (e:[pAnd (ei:(PNot <$> filter (==ei) es)) | ei <- es])
isSensible _ _ 
  = return True 

isNumeric :: Sort -> Bool 
isNumeric FInt = True 
isNumeric (FVar  _) = True 
isNumeric (FObj _) = True 
isNumeric _ = False

isList :: Sort -> Bool 
isList (FApp l _) = isList l 
isList (FTC c)    = isListTC c 
isList _          = False


unPAnd :: Expr -> Expr 
unPAnd (PAnd [e]) = unPAnd e
unPAnd e          = e  

isLocal :: GWInfo -> Expr -> SolveM Bool 
isLocal i e = do 
  let (bsE,eE) = grepIApps (gsym i) e 
  let (bsA,eA) = grepApps eE 
  let ee = PExist bsA (PExist ((gsym i, gsort i):bsE) eA)
  rr <- isValid  ee
  -- liftIO $ putStrLn ("isLocal " ++ pretty ee ++ " = " ++ show rr)
  return rr  


-- implemented as not contradicts
isMoreSpecific :: GWInfo -> Expr -> SolveM Bool
-- isMoreSpecific _ _ = return True 
isMoreSpecific i e = do 
  let ee' = e `PImp` gexpr i
  let (bsE,eE) = grepIApps (gsym i) ee' 
  let (bsA,eA) = grepApps eE 
  let ee = PAll ((gsym i, gsort i):(bsE ++ bsA)) eA
  rr <- isValid ee 
  -- liftIO $ putStrLn ("isMoreSpecific " ++ pretty ee ++ " = " ++ show rr)
  return rr 

isValid :: Expr -> SolveM Bool
isValid e 
  | isContraPred e = return False 
  | isTautoPred  e = return True 
  | (PImp _ ee) <- e
  , isTautoPred ee = return True 
  | PImp (PAnd es) e2 <- e 
  , e2 `elem` es    = return True    
isValid e = do 
  r <- not <$> checkSat (PNot e)
  -- liftIO $ putStrLn ("CHECK SAT FOR " ++ pretty (PNot e) ++ "RES = " ++ show r)
  return r 



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
      = let (bs',e') = getApp ee  in (bs ++ bs',e') 
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
    go bs (PImp e1 e2)
      = let (bs1, e1') = go [] e1 in 
        let (bs2, e2') = go [] e2 in 
        (concat [bs, bs1, bs2], PImp e1' e2')
    go bs e 
      = (bs, e)

    unCst (ECst e _) = unCst e
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
      | (unCst e2) == EVar i 
      = let (bs', e') = getApp ee in (bs ++ bs', e')   
      | otherwise
      = (bs, EApp e1 e2)
    go bs (ECst e _)
      = go bs e 
    go bs (PImp e1 e2)
      = let (bs1, e1') = go [] e1 in 
        let (bs2, e2') = go [] e2 in 
        (concat [bs, bs1, bs2], PImp e1' e2')
    go bs (PAnd es)
      = let (bs', es') = unzip $ map (go bs) es in 
        (concat bs', PAnd es')
    go bs (POr es)
      = let (bs', es') = unzip $ map (go bs) es in 
        (concat bs', POr es')
    go bs e 
      = (bs, e)

    unCst (ECst e _) = unCst e
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
exprSort (ECon (I _))   = Just FInt
exprSort (ECon (R _))   = Just FReal
exprSort (ECon (L _ s)) = Just s
exprSort _ = Nothing 

