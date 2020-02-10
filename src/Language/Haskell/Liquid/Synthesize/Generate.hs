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

-- Generate terms that have type t: This changes the @ExprMem@ in @SM@ state.
-- Return expressions type checked against type @specTy@.
genTerms :: String -> SpecType -> SM [CoreExpr] 
genTerms s specTy = 
  do  funTyCands <- withInsProdCands specTy
      es <- withTypeEs s specTy
      main <- filterElseM (hasType " genTerms " True specTy) (tracepp (s ++ " { Functions " ++ concat (map getVn funTyCands) ++ " } [ genTerms ] ES = ") es) $ 
                withDepthFill s specTy 0 funTyCands
      return (tracepp (" main for " ++ s) main)

genTerms0 :: String -> SpecType -> SM [CoreExpr] 
genTerms0 s specTy = 
  do  funTyCands <- withInsProdCands specTy
      es <- withTypeEs s specTy
      res <-  filterElseM (hasType " genTerms0 " True specTy) es $
                withDepthFill0 specTy 0 funTyCands 
      return (tracepp " [ genTerms0 ] Returns " res)

withDepthFill0 :: SpecType -> Int -> [(Symbol, (Type, Var))] -> SM [CoreExpr]
withDepthFill0 t depth funTyCands = do
  curEm <- sExprMem <$> get
  exprs <- fillMany0 depth curEm funTyCands []

  what <- filterElseM (hasType " withDepthFill0 " True t) exprs $ 
            if depth < maxAppDepth
              then withDepthFill0 t (depth + 1) funTyCands
              else return []
  return (tracepp " [ withDepthFill0 ] Returns " what)

fillMany0 :: Int -> ExprMemory -> [(Symbol, (Type, Var))] -> [CoreExpr] -> SM [CoreExpr] 
fillMany0 _     _       []             accExprs = return (tracepp " [ fillMany0 ] Returns " accExprs)
fillMany0 depth exprMem (cand : cands) accExprs = do
  let (_, (htype, _))   = cand
      subgoals'         = createSubgoals htype 
      resultTy          = last subgoals' 
      subgoals          = take (length subgoals' - 1) subgoals'
      argCands          = map (withSubgoal exprMem) subgoals 
      -- Checks if there is an empty list of of produced candidate terms for @cand@
      check             = foldr (\l b -> null l || b) False argCands 

  if check
    then do fillMany0 depth exprMem cands accExprs 
    else do curAppDepth <- sAppDepth <$> get 
            newExprs <- repeatPrune curAppDepth 1 (length argCands) cand argCands []
            let nextEm = map (resultTy, , curAppDepth + 1) newExprs
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
            let accExprs' = newExprs ++ accExprs
            fillMany0 depth exprMem cands accExprs' 

--  | @withDepthFill@
withDepthFill :: String -> SpecType -> Int -> [(Symbol, (Type, Var))] -> SM [CoreExpr]
withDepthFill s t depth funTyCands = do
  curEm <- sExprMem <$> get
  exprs <- fillMany s depth curEm funTyCands []

  what2 <- filterElseM (hasType " withDepthFill " True t) exprs $
            if depth < maxAppDepth
              then withDepthFill s t (depth + 1) funTyCands
              else return [] 
  return (tracepp (s ++ " what2 ") what2)


-- Produce new expressions from expressions currently in expression memory (ExprMemory).
-- Only candidate terms with function type (funTyCands) can be passed as second argument.
-- This function (@fillMany@) performs (full) application for candidate terms, 
-- where candidate is a function from our environment.
--              | expression memory  |
--              | before the function|                   | terms that   |
--              | is called (does    |                   | are produced |
--              | not change)        |                   | by `fillMany |
fillMany :: String -> Int -> ExprMemory -> [(Symbol, (Type, Var))] -> [CoreExpr] -> SM [CoreExpr] 
fillMany s _     _       []             accExprs = return (tracepp (" [ fillMany ] " ++ s ++  " Returns ") accExprs)
fillMany s depth exprMem (cand : cands) accExprs = do
  let (_, (htype, v))   = cand
      subgoals'         = createSubgoals htype 
      resultTy          = last subgoals' 
      subgoals          = take (length subgoals' - 1) subgoals'
      argCands          = map (withSubgoal exprMem) subgoals 
      -- Checks if there is an empty list of of produced candidate terms for @cand@
      check             = foldr (\l b -> null l || b) False argCands 

  if (tracepp (" [ Candidates ] For " ++ show v ++ " subgoals = " ++ concat (map showTy subgoals')) check)
    then do curAppDepth <- sAppDepth <$> get 
            goals <- liftCG $ mapM trueTy subgoals 
            argCands0 <- mapM (genTerms0 " fillMany0 calls genTerms0 ") goals
            let argCands1 = map (map (, curAppDepth + 1)) argCands0
            exprs0 <- repeatPrune curAppDepth 1 (length argCands1) cand argCands1 []
            let nextEm = map (resultTy, , curAppDepth + 1) exprs0 
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
            let accExprs' = exprs0 ++ accExprs 
            fillMany (" | " ++ show v ++ " TRUE CHECK | " ++ s) depth exprMem cands accExprs'
    else do curAppDepth <- sAppDepth <$> get 
            newExprs <- repeatPrune curAppDepth 1 (length argCands) cand argCands []
            let nextEm = map (resultTy, , curAppDepth + 1) newExprs
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
            let accExprs' = newExprs ++ accExprs
            -- trace (" [ fillMany < " ++ show depth ++ " > for cand " ++ show (fst cand) ++ 
            --        " argCands "  ++ show argCands ++ " Expressions: " ++ show (length newExprs) ++ "] \n" ++ 
            --        show accExprs') $ 
            fillMany (" | " ++ show v ++ " FALSE CHECK | " ++ s) depth exprMem cands accExprs' 


-------------------------------------------------------------------------------------------
-- |                       Pruning terms for function application                      | --
-------------------------------------------------------------------------------------------

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
    else return (tracepp (" [ repeatPrune ] For " ++ show (fst toBeFilled) ++ " result = ") acc)

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
      v'' = apply (if v == xtop then uniVars else tvs) (GHC.Var v)
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

-- Misc
getVn :: (Symbol, (Type, Var)) -> String 
getVn (_, (t, vn)) = " | For candidate " ++ show vn ++ " type = " ++ showTy t ++ " | "

getVars0 :: [(Symbol, (Type, Var))] -> [Var] 
getVars0 []                 = []
getVars0 ((_, (_, v)) : vs) = v : getVars0 vs

getExprs0 :: ExprMemory -> [GHC.CoreExpr]
getExprs0 []             = []
getExprs0 ((_, e, _):es) = e : getExprs0 es
