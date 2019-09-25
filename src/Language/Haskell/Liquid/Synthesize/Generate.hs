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
import           Language.Haskell.Liquid.Constraint.Generate (consE)
import           Language.Haskell.Liquid.Synthesize.Check

import CoreUtils (exprType)
import CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import Var 

import           Data.Maybe
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Language.Haskell.Liquid.GHC.TypeRep

import           Debug.Trace 

import           Language.Haskell.Liquid.GHC.Play (isHoleVar)

-- Generate terms that have type t
genTerms :: SpecType -> SM [CoreExpr] 
genTerms specTy = 
  do  senv <- ssEnv <$> get
      mbTyVar <- sGoalTyVar <$> get
      let goalTyVar = fromJust mbTyVar
          τ            = toType specTy
          noHolesEnv   = M.fromList $ filter (\(_, (_, v)) -> not $ isHoleVar v) (M.toList senv)
          cands        = findCandidates senv τ
          filterFunFun   (_, (ty, _)) = not $ isBasic ty
          funTyCands'  = filter filterFunFun cands

          funTyCands  = 
            map (\(s, (ty, v)) -> 
                let e = instantiate (GHC.Var v) (TyVarTy goalTyVar)
                    ty' = exprType e
                in (s, (ty', v))) funTyCands' 
          
          noHoles      = filter (\(_, (_, v)) -> not $ isHoleVar v) funTyCands 

          initEMem'    = initExprMem senv
          initEMem     = 
            map (\(t, e, i) -> 
              let e' = instantiate e (TyVarTy goalTyVar)
                  t' = exprType e'
              in  (t', e', i)) initEMem' 

      modify (\s -> s { sAppDepth = 0 })
      finalEMem <- withDepthFill 0 initEMem funTyCands
      let result = takeExprs $ filter (\(t, _, _) -> t == τ) finalEMem 
      notWellTyped <- filterM (composeM isWellTyped not) result
      trace ("\n[ Well-typed expressions ] " ++ show notWellTyped ++ "\n expressions " ++ show (map (\e -> show (fst $ fromAnf e [])) result)) $
        return result

instantiate :: CoreExpr -> Type -> CoreExpr
instantiate e t = 
  case exprType e of 
    ForAllTy {} -> GHC.App e (GHC.Type t)
    _           -> e

-- PB: We need to combine that with genTerms and synthesizeBasic
withDepthFill :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> SM ExprMemory
withDepthFill depth exprMem funTyCands = do 
  exprMem' <- fillMany depth exprMem funTyCands exprMem
  curAppDepth <- sAppDepth <$> get
  if depth < maxAppDepth
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
pruneCands depth lst = filter (\(_, i) -> i >= depth) lst

type Depth = Int
type Up    = Int
type Down  = Int
repeatPrune :: Depth -> Up -> Down -> (Symbol, (Type, Var)) -> [[(CoreExpr, Int)]] -> [CoreExpr] -> SM [CoreExpr]
repeatPrune depth down up toBeFilled cands acc =
  if down <= up 
    then do 
      let cands' = updateIthElem down depth cands 
      acc' <- (++ acc) <$> fillOne toBeFilled cands'
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
      accExprs'  <- 
        (++ accExprs) . map (resultTy, , depth + 1) <$> 
          repeatPrune depth 1 (length argCands) cand argCands []
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


findCandidates :: SSEnv -> Type -> [(Symbol, (Type, Var))]
findCandidates senv goalTy = 
  let senvLst   = M.toList senv
      senvLst'  = map (\(sym, (spect, var)) -> (sym, (toType spect, var))) senvLst
      filterFun (_, (specT, _)) = goalType goalTy specT
      candTerms = filter filterFun senvLst'
  in  candTerms

