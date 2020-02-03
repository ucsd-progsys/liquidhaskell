{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Generate where

import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Haskell.Liquid.Synthesize.GHC hiding (SSEnv)
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import           Language.Haskell.Liquid.Synthesize.Check

import CoreUtils (exprType)
import CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import Var 

import           Data.Maybe
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Fixpoint.Types.PrettyPrint
import           Debug.Trace 

-- Generate terms that have type t: This changes the ExprMem in SM state.
-- Return expressions type checked against type t.
genTerms :: SpecType -> SM [CoreExpr] 
genTerms specTy = 
  do  funTyCands <- withInsProdCands specTy

      es <- withTypeEs specTy

      filterElseM (hasType specTy) es $ 

        withDepthFill specTy 0 funTyCands 

--  | @withDepthFill@
withDepthFill :: SpecType -> Int -> [(Symbol, (Type, Var))] -> SM [CoreExpr]
withDepthFill t depth funTyCands = do
  curEm <- sExprMem <$> get
  exprs <- fillMany depth curEm funTyCands []

  filterElseM (hasType t) exprs $
    -- TODO review the following line
    -- modify (\s -> s { sAppDepth = sAppDepth s + 1 })
    if depth < maxAppDepth
      then withDepthFill t (depth + 1) funTyCands
      else return [] -- Note: checkedEs == [] at this point


-- Note: @i@, the 1st argument of @updateIthElem@ should be an 1-based index.
updateIthElem :: Int -> Int -> [[(CoreExpr, Int)]] -> ([[(CoreExpr, Int)]], [[(CoreExpr, Int)]])
updateIthElem _ _     []  = ([], [])
updateIthElem i depth lst = 
  case pruned of 
    [] -> ([], [])
    _  -> (left ++ [pruned] ++ right, left ++ [others] ++ right)
  where left   = take (i-1) lst
        cur    = lst !! (i-1)
        right  = drop i lst
        pruned = pruneCands depth cur
        others = noDuples depth cur


pruneCands :: Int -> [(CoreExpr, Int)] -> [(CoreExpr, Int)]
pruneCands depth lst = filter (\(_, i) -> i >= depth) lst

noDuples :: Int -> [(CoreExpr, Int)] -> [(CoreExpr, Int)]
noDuples depth lst = filter (\(_, i) -> i < depth) lst

type Depth = Int
type Up    = Int
type Down  = Int
repeatPrune :: Depth -> Up -> Down -> (Symbol, (Type, Var)) -> [[(CoreExpr, Int)]] -> [CoreExpr] -> SM [CoreExpr]
repeatPrune depth down up toBeFilled cands acc = 
--  trace (" [ repeatPrune " ++ show depth ++"] for " ++ show (fst toBeFilled) ++ " Cands " ++ show cands) $ 
  if down <= up 
    then do 
      let (cands', cands'') = updateIthElem down depth cands 
      es <- fillOne toBeFilled cands'
      acc' <- (++ acc) <$> filterM isWellTyped es
      -- trace ("For down = " ++ show down ++ " cs' " ++ show cands' ++ " cs'' " ++ show cands'') $ 
      repeatPrune depth (down + 1) up toBeFilled cands'' acc'
    else return acc



-- Produce new expressions from expressions currently in expression memory (ExprMemory).
-- Only candidate terms with function type (funTyCands) can be passed as second argument.
-- This function (@fillMany@) performs (full) application for candidate terms, 
-- where candidate is a function from our environment.
--              | expression memory  |
--              | before the function|                   | terms that   |
--              | is called (does    |                   | are produced |
--              | not change)        |                   | by `fillMany |
fillMany :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> [CoreExpr] -> SM [CoreExpr] 
fillMany _     _       []             accExprs = return accExprs
fillMany depth exprMem (cand : cands) accExprs = do
  let (_, (htype, _))   = cand
      subgoals'         = createSubgoals htype 
      resultTy          = last subgoals' 
      subgoals          = take (length subgoals' - 1) subgoals'
      argCands          = map (withSubgoal exprMem) subgoals 
      check             = foldr (\l b -> null l || b) False argCands 

  if check 
    then fillMany depth exprMem cands accExprs 
    else do
      curAppDepth <- sAppDepth <$> get 
      newExprs <- repeatPrune curAppDepth 1 (length argCands) cand argCands []
      let nextEm = map (resultTy, , curAppDepth + 1) newExprs
      modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
      let accExprs' = newExprs ++ accExprs
      -- trace (
      --   " [ fillMany <" ++ show depth ++ 
      --   "> for cand " ++ show (fst cand) ++ 
      --   " argCands "  ++ show argCands ++
      --   " Expressions: " ++ show (length newExprs) ++ 
      --   "] \n" ++ show accExprs') $ 
      fillMany depth exprMem cands accExprs'

-- {applyOne, applyNext, applyMany} are auxiliary functions for `fillOne`
applyOne :: Var -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyOne v args typeOfArgs = do
  idx <- incrSM
  mbTyVar <- sGoalTyVar <$> get
  let tyvar = fromMaybe (error "No type variables in the monad!") mbTyVar
  v'' <- case varType v of
            ForAllTy{} -> return $ GHC.App (GHC.Var v) (GHC.Type (TyVarTy tyvar))
            _          -> return $ GHC.Var v
  return 
    [ let letv' = mkVar (Just "x") idx typeOfArgs
      in  case v' of 
            GHC.Var _ -> GHC.App v'' v' 
            _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App v'' (GHC.Var letv')) | (v', _) <- args ] 

applyNext :: [CoreExpr] -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyNext apps args typeOfArgs = do 
  !idx  <- incrSM
  return 
    [ case v'' of 
        GHC.Var _ -> GHC.App v' v''
        _         ->
          let letv'' = mkVar (Just "x") idx typeOfArgs 
          in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App v' (GHC.Var letv''))
    | v' <- apps, (v'', _) <- args
    ]

applyMany :: [CoreExpr] -> [[(CoreExpr, Int)]] -> [Type] -> SM [CoreExpr] 
applyMany exprs []             []                         = return exprs
applyMany exprs (args : args') (typeOfArgs : typeOfArgs') = do
  exprs' <- applyNext exprs args typeOfArgs
  applyMany exprs' args' typeOfArgs'
applyMany _     _              _                          = error "applyMany wildcard"

-- Takes a function and a list of correct expressions for every argument
-- and returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[(CoreExpr, Int)]] -> SM [CoreExpr] 
fillOne _           []                   = return []
fillOne (_, (t, v)) (argCand : argCands) = do 
  let sg'     = createSubgoals t 
      sg      = take (length sg' - 1) sg'
      argType = head sg 
  exprs <- applyOne v argCand argType
  applyMany exprs argCands (tail sg) 


-- withSubgoal :: a type from subgoals 
-- Returns all expressions in ExprMemory that have the same type.
withSubgoal :: ExprMemory -> Type -> [(CoreExpr, Int)]
withSubgoal []               _ = []
withSubgoal ((t, e, i) : exprs) τ = 
  if τ == t 
    then (e, i) : withSubgoal exprs τ
    else withSubgoal exprs τ
