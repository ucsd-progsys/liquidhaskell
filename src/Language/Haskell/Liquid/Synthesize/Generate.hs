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


-- PB: Currently, works with arity 1 or 2 (see below)...
-- Also, I don't think that it works for higher order e.g. map :: (a -> b) -> [a] -> [b].
-- Takes a function and a list of correct expressions for every argument
-- and returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[CoreExpr]] -> SM [CoreExpr]
fillOne funTyCand argCands = 
  let (_, (t, v)) = funTyCand
      arity       = length argCands 
      sg'         = createSubgoals t 
      sg          = take (length sg' - 1) sg'
  in  if arity == 1 
        then  do  idx <- incrSM 
                  return [ 
                    let letv' = mkVar (Just "x") idx (head sg)
                    in  case v' of 
                          GHC.Var _ -> GHC.App (GHC.Var v) v' 
                          _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App (GHC.Var v) (GHC.Var letv')) | v' <- head argCands ]
        else  if arity == 2
                then do
                  !idx  <- incrSM  
                  !idx' <- incrSM 

                  return 
                    [ case v' of 
                        GHC.Var _ -> 
                          case v'' of 
                            GHC.Var _ -> GHC.App (GHC.App (GHC.App (GHC.Var v) (GHC.Type (head sg))) v') v'' 
                            _         -> 
                              let letv'' = mkVar (Just "x") idx' (sg !! 1)
                              in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App (GHC.App (GHC.App (GHC.Var v) (GHC.Type (head sg)) ) v') (GHC.Var letv'')) 
                        _         -> 
                          let letv' = mkVar (Just "x") idx (head sg) 
                          in  GHC.Let (GHC.NonRec letv' v') (
                            case v'' of
                              GHC.Var _ -> 
                                GHC.App (GHC.App (GHC.Var v) (GHC.Var letv')) v''
                              _         -> 
                                let letv'' = mkVar (Just "x") idx' (sg !! 1) 
                                in  GHC.Let (GHC.NonRec letv'' v'') (GHC.App (GHC.App (GHC.Var v) (GHC.Var letv')) (GHC.Var letv'')))
                        | v'  <- head argCands, 
                          v'' <- argCands !! 1
                    ]
                else error $ "[ fillOne ] Function: " ++ show v

genApp :: (Symbol, (Type, Var)) -> [[CoreExpr]] -> [Type] -> SM [CoreExpr]
genApp _      []           []       = return []
genApp ftcand (arg : args) (t : ts) = do
  let (_, (t, v)) = ftcand
      -- arity       = length argCands 
      -- sg'         = createSubgoals t 
      -- sg          = take (length sg' - 1) sg' 
  idx <- incrSM
  return 
    [ let letv' = mkVar (Just "x") idx t
      in  case v' of 
            GHC.Var _ -> GHC.App (GHC.Var v) v' 
            _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App (GHC.Var v) (GHC.Var letv')) | v' <- arg ]
genApp _     _           _          = error "[ genApp ] types and terms mismatch"

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

