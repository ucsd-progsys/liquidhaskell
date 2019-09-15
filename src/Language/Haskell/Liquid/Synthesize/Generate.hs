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


          initEMem     = initExprMemory τ senv
      finalEMem <- withDepthFill maxAppDepth initEMem funTyCands
      let result       = takeExprs $ filter (\(t, _) -> t == τ) finalEMem 
      -- trace ("\n[ Expressions ] " ++ show result) $
      return result

maxAppDepth :: Int 
maxAppDepth = 4

-- PB: We need to combine that with genTerms and synthesizeBasic
withDepthFill :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> SM ExprMemory
withDepthFill depth exprMem funTyCands = do 
  exprMem' <- fillMany exprMem funTyCands exprMem
  if depth > 0 
    then withDepthFill (depth - 1) exprMem' funTyCands
    else return exprMem 

type ExprMemory = [(Type, CoreExpr)]
-- Initialized with basic type expressions
-- e.g. b  --- x_s3
--     [b] --- [], x_s0, x_s4
initExprMemory :: Type -> SSEnv -> ExprMemory
initExprMemory τ ssenv = 
  let senv    = M.toList ssenv 
      senv'   = filter (\(_, (t, _)) -> isBasic (toType t)) senv 
      senv''  = map (\(_, (t, v)) -> (toType t, GHC.Var v)) senv' 
      senv''' = map (\(t, e) -> (instantiateType τ t, e)) senv''
  in  senv'''


-- Produce new expressions from expressions currently in expression memory (ExprMemory).
-- Only candidate terms with function type (funTyCands) can be passed as second argument.
fillMany :: ExprMemory -> [(Symbol, (Type, Var))] -> ExprMemory -> SM ExprMemory 
fillMany _       []             accExprs = return accExprs
fillMany exprMem (cand : cands) accExprs = do
  let (_, (htype, _))   = cand
      subgoals'         = createSubgoals htype 
      resultTy          = last subgoals' 
      subgoals          = take (length subgoals' - 1) subgoals'
      argCands          = map (withSubgoal exprMem) subgoals 
      
  withType <- fillOne cand argCands
  let newExprs          = map (resultTy, ) withType
      accExprs'         = accExprs ++ newExprs
  fillMany exprMem cands accExprs'

-- {applyOne, applyNext, applyMany} are auxiliary functions for `fillOne`
applyOne :: Var -> [CoreExpr] -> Type -> SM [CoreExpr]
applyOne v args typeOfArgs = do
  idx <- incrSM
  let v'' = case varType v of
              ForAllTy{} -> GHC.App (GHC.Var v) (GHC.Type typeOfArgs)
              _          -> GHC.Var v
  return 
    [ let letv' = mkVar (Just "x") idx typeOfArgs
      in  case v' of 
            GHC.Var _ -> GHC.App v'' v' 
            _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App v'' (GHC.Var letv')) | v' <- args ] 

applyNext :: [CoreExpr] -> [CoreExpr] -> Type -> SM [CoreExpr]
applyNext apps args typeOfArgs = do 
  !idx  <- incrSM
  return 
    [ case v'' of 
        GHC.Var _ -> GHC.App v' v''
        _         ->
          let letv'' = mkVar (Just "x") idx typeOfArgs 
          in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App v' (GHC.Var letv''))
    | v' <- apps, v'' <- args
    ]

applyMany :: [CoreExpr] -> [[CoreExpr]] -> [Type] -> SState -> ([CoreExpr], SState)
applyMany exprs []             []                         st = (exprs, st)
applyMany exprs (args : args') (typeOfArgs : typeOfArgs') st = 
  let (exprs', st') = unsafePerformIO $ runStateT (applyNext exprs args typeOfArgs) st 
  in  applyMany exprs' args' typeOfArgs' st'
applyMany _     _              _                          _  = error "applyMany wildcard"

-- Takes a function and a list of correct expressions for every argument
-- and returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[CoreExpr]] -> SM [CoreExpr] 
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
withSubgoal :: ExprMemory -> Type -> [CoreExpr]
withSubgoal []               _ = []
withSubgoal ((t, e) : exprs) τ = 
  if τ == t 
    then e : withSubgoal exprs τ
    else withSubgoal exprs τ


findCandidates :: SSEnv -> Type -> [(Symbol, (Type, Var))]
findCandidates senv goalTy = 
  let senvLst   = M.toList senv
      senvLst'  = map (\(sym, (spect, var)) -> (sym, (toType spect, var))) senvLst
      filterFun (_, (specT, _)) = goalType goalTy specT
      candTerms = filter filterFun senvLst'
  in  candTerms

