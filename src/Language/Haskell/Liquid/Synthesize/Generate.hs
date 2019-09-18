{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Generate where

import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Haskell.Liquid.Synthesize.GHC
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)

import CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import Var 

import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Language.Haskell.Liquid.GHC.TypeRep

import           Debug.Trace 

import           System.IO.Unsafe

-- Generate terms that have type t
genTerms :: SpecType -> SM [CoreExpr] 
genTerms specTy = 
  do  senv <- ssEnv <$> get
      let τ            = toType specTy
          cands        = findCandidates senv τ
          filterFunFun   (_, (ty, _)) = not $ isBasic ty
          funTyCands'  = filter filterFunFun cands
          funTyCands   = map (\(s, (ty, v)) -> (s, (instantiateType τ ty, v))) funTyCands'


          initEMem'    = initExprMem senv
          initEMem     = map (\(t, e, i) -> (instantiateType τ t, e, i)) initEMem' 

      modify (\s -> s { sAppDepth = 0 })
      finalEMem <- withDepthFill 0 initEMem funTyCands
      let result       = takeExprs $ filter (\(t, _, _) -> t == τ) finalEMem 

      -- trace ("\n[ Expressions ] " ++ show result) $
      return result


-- PB: We need to combine that with genTerms and synthesizeBasic
withDepthFill :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> SM ExprMemory
withDepthFill depth exprMem funTyCands = do 
  exprMem' <- fillMany depth exprMem funTyCands exprMem
  curAppDepth <- sAppDepth <$> get
  if depth < maxAppDepth {- curAppDepth <= maxAppDepth -}
    then do
      modify (\s -> s { sAppDepth = curAppDepth + 1 })
      withDepthFill (depth + 1) exprMem' funTyCands
    else do
      modify (\s -> s { sAppDepth = curAppDepth + 1 })
      return exprMem 


-- Note: i should be 1-based index
updateIthElem :: Int -> Int -> [[(CoreExpr, Int)]] -> [[(CoreExpr, Int)]]
updateIthElem i depth lst = 
  case pruned of 
    [] -> []
    _  -> left ++ [pruned] ++ right
  where left   = take (i-1) lst
        cur    = lst !! (i-1)
        right  = drop i lst
        pruned = pruneCands depth cur


pruneCands :: Int -> [(CoreExpr, Int)] -> [(CoreExpr, Int)]
pruneCands depth lst = filter (\(e, i) -> i >= depth) lst

-- depth, down limit, up limit, candidates: input
repeatPrune :: Int -> Int -> Int -> (Symbol, (Type, Var)) -> [[(CoreExpr, Int)]] -> [CoreExpr] -> SM [CoreExpr]
repeatPrune depth down up toBeFilled cands acc = do
  if down <= up 
    then do 
      curState <- get
      let cands' = updateIthElem down depth cands 
          (acc', st1) = 
            case cands' of 
              [] -> (acc, curState)
              _  -> 
                let (exprs', st') = unsafePerformIO $ runStateT (fillOne toBeFilled cands') curState
                in  (exprs' ++ acc, st')
      put st1
      repeatPrune depth (down + 1) up toBeFilled cands acc'
    else return acc



-- Produce new expressions from expressions currently in expression memory (ExprMemory).
-- Only candidate terms with function type (funTyCands) can be passed as second argument.
fillMany :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> ExprMemory -> SM ExprMemory 
fillMany _ _       []             accExprs = return accExprs
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

      curState <- get
      let (newExprs, st)    = 
            case argCands of 
              [] -> ([], curState)
              _  ->
                if (maximum . map (maximum . map snd)) argCands < depth
                  then ([], curState)
                  else 
                    let (withType, st') = unsafePerformIO $ runStateT (repeatPrune depth 1 (length argCands) cand argCands []) curState
                    in  (map (resultTy, , depth + 1) withType, st')
          accExprs'         = accExprs ++ newExprs
      put st
      -- trace (
      --   " [ expressions " ++ show depth ++ 
      --   ", arguments = " ++ show (length argCands) ++ 
      --   " , candidates of arguments " ++ show (map length argCands) ++ 
      --   " ] " ++ showEmem accExprs') $ 
      fillMany depth exprMem cands accExprs'

-- {applyOne, applyNext, applyMany} are auxiliary functions for `fillOne`
applyOne :: Var -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyOne v args typeOfArgs = do
  idx <- incrSM
  let v'' = case varType v of
              ForAllTy{} -> GHC.App (GHC.Var v) (GHC.Type typeOfArgs)
              _          -> GHC.Var v
  return 
    [ let letv' = mkVar (Just "x") idx typeOfArgs
      in  case v' of 
            GHC.Var _ -> GHC.App v'' v' 
            _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App v'' (GHC.Var letv')) | (v', i) <- args ] 

applyNext :: [CoreExpr] -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyNext apps args typeOfArgs = do 
  !idx  <- incrSM
  return 
    [ case v'' of 
        GHC.Var _ -> GHC.App v' v''
        _         ->
          let letv'' = mkVar (Just "x") idx typeOfArgs 
          in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App v' (GHC.Var letv''))
    | v' <- apps, (v'', i) <- args
    ]

applyMany :: [CoreExpr] -> [[(CoreExpr, Int)]] -> [Type] -> SState -> ([CoreExpr], SState)
applyMany exprs []             []                         st = (exprs, st)
applyMany exprs (args : args') (typeOfArgs : typeOfArgs') st = 
  let (exprs', st') = unsafePerformIO $ runStateT (applyNext exprs args typeOfArgs) st 
  in  applyMany exprs' args' typeOfArgs' st'
applyMany _     _              _                          _  = error "applyMany wildcard"

-- Takes a function and a list of correct expressions for every argument
-- and returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[(CoreExpr, Int)]] -> SM [CoreExpr] 
fillOne funTyCand argCands = do 
  let (_, (t, v)) = funTyCand 
      sg'         = createSubgoals t 
      sg          = take (length sg' - 1) sg'
      withTypeIns = head sg 
  exprs <- applyOne v (head argCands) withTypeIns 
  st <- get 
  let (exprs', st') = applyMany exprs (tail argCands) (tail sg) st
  put st'
  return exprs'


-- withSubgoal :: a type from subgoals 
-- Returns all expressions in ExprMemory that have the same type.
withSubgoal :: ExprMemory -> Type -> [(CoreExpr, Int)]
withSubgoal []               _ = []
withSubgoal ((t, e, i) : exprs) τ = 
  if τ == t 
    then (e, i) : withSubgoal exprs τ
    else withSubgoal exprs τ


findCandidates :: SSEnv -> Type -> [(Symbol, (Type, Var))]
findCandidates senv goalTy = 
  let senvLst   = M.toList senv
      senvLst'  = map (\(sym, (spect, var)) -> (sym, (toType spect, var))) senvLst
      filterFun (_, (specT, _)) = goalType goalTy specT
      candTerms = filter filterFun senvLst'
  in  candTerms

