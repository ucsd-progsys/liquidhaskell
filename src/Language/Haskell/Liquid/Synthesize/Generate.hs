{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Generate where

import           Language.Haskell.Liquid.Types hiding (SVar)
import           Language.Haskell.Liquid.Synthesize.GHC hiding (SSEnv)
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc hiding (notrace)
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
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)

getVars0 :: [(Symbol, (Type, Var))] -> [Var] 
getVars0 []                 = []
getVars0 ((_, (_, v)) : vs) = v : getVars0 vs

getExprs0 :: ExprMemory -> [GHC.CoreExpr]
getExprs0 []             = []
getExprs0 ((_, e, _):es) = e : getExprs0 es

-- Generate terms that have type t: This changes the @ExprMem@ in @SM@ state.
-- Return expressions type checked against type @specTy@.
genTerms :: SpecType -> SM [CoreExpr] 
genTerms specTy = notrace ( " [ genTerms ] specTy = " ++ show specTy) $
  do  funTyCands <- withInsProdCands specTy

      sEMem <- getSEMem

      es <- withTypeEs (tracepp (" [ genTerms ] ExprMemory = " ++ show (getExprs0 sEMem) ++ " and specTy = ") specTy)

      filterElseM (hasType specTy) (tracepp " [ genTerms ] es = " es) $ 

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

getVarName :: (Symbol, (Type, Var)) -> Var 
getVarName (_, (_, vn)) = vn

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
      -- Checks if there is an empty list of of produced candidate terms for @cand@
      check             = foldr (\l b -> null l || b) False argCands 

  if check
    then do fillMany depth exprMem cands accExprs 
    else do curAppDepth <- sAppDepth <$> get 
            newExprs <- repeatPrune curAppDepth 1 (length argCands) cand argCands []
            let nextEm = map (resultTy, , curAppDepth + 1) newExprs
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
            let accExprs' = newExprs ++ accExprs
            trace (" [ fillMany < " ++ show depth ++ " > for cand " ++ show (fst cand) ++ 
                   " argCands "  ++ show argCands ++ " Expressions: " ++ show (length newExprs) ++ "] \n" ++ 
                   show accExprs') $ fillMany depth exprMem cands accExprs' 

----------------------------------------------------------------------------
--  | Term generation: Perform type and term application for functions. | --
----------------------------------------------------------------------------

--  | @fillOne@ : Takes a function @1@ and 
--    @2@ a list of expressions for every argument of the function.
--    @2@ contains expressions with the same type as the input types of @1@.
--  > Returns a list of new expressions.
fillOne :: (Symbol, (Type, Var)) -> [[(CoreExpr, Int)]] -> SM [CoreExpr] 
fillOne _           []                   = return []
fillOne (_, (t, v)) (argCand : argCands) = do 
  -- 1. Perform type applications (if needed)
  exprs <- applyOne v argCand t0 -- argType
  -- 2. Perform term applications 
  applyMany exprs argCands ts 
  where   (t0, ts) = safeSubgoals t

--  | @applyOne@, @applyNext@, @applyMany@ are auxiliary functions for @fillOne@

--  | @applyOne@ performs type applications if needed.
applyOne :: Var -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyOne v args typeOfArgs = do
  xtop    <- getSFix
  uniVars <- getSUniVars
  idx <- incrSM
  mbTyVar <- sGoalTyVar <$> get
  let tvs = fromMaybe (error "No type variables in the monad!") mbTyVar
  v'' <- return (apply (if v == xtop then uniVars else tvs) (GHC.Var v))
  return 
    [ let letv' = mkVar (Just "x") idx typeOfArgs
      in  case v' of 
            GHC.Var _ -> GHC.App v'' v' 
            _         -> GHC.Let (GHC.NonRec letv' v') (GHC.App v'' (GHC.Var letv')) | (v', _) <- args ] 

-- | @applyNext@
--    Term application: Applies each one of @args@ to each one of @apps@.
--    Produces (number of @apps@ * number of @args@) expressions.
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

-- |  @applyMany@ Performs full term application by executing @applyNext@ 
--    for every argument of the candidate function of @fillOne@.
applyMany :: [CoreExpr] -> [[(CoreExpr, Int)]] -> [Type] -> SM [CoreExpr] 
applyMany exprs []             []                         = return exprs
applyMany exprs (args : args') (typeOfArgs : typeOfArgs') = do
  exprs' <- applyNext exprs args typeOfArgs
  applyMany exprs' args' typeOfArgs'
applyMany _     _              _                          = error "applyMany wildcard"

-- | @safeSubgoals@: For the input types of @t@, returns a tuple of 
--   the 1st input type and the rest input types.
--   @t@ is a function type. Otherwise, it throws an error.
safeSubgoals :: Type -> (Type, [Type])
safeSubgoals t = 
  case ts of  [ ]     -> error $ " [ safeSubgoals ] Should be a function type " ++ showTy t 
              t : ts' -> (t, ts') 
  where subgoals = createSubgoals t                    -- Includes the result type 
        ts       = take (length subgoals - 1) subgoals -- Input types from the subgoals

-- @withSubgoal@ :: Takes a subgoal type, and 
-- returns all expressions in @ExprMemory@ that have the same type.
withSubgoal :: ExprMemory -> Type -> [(CoreExpr, Int)]
withSubgoal []                  _ = []
withSubgoal ((t, e, i) : exprs) τ = 
  if τ == t 
    then (e, i) : withSubgoal exprs τ
    else withSubgoal exprs τ
