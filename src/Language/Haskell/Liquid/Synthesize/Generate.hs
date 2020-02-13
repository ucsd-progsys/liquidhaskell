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
import           Data.Tuple.Extra 
import           Data.List 

-- Generate terms that have type t: This changes the @ExprMemory@ in @SM@ state.
-- Return expressions type checked against type @specTy@.
genTerms :: String -> SpecType -> SM [CoreExpr] 
genTerms = genTerms' ResultMode 


data SearchMode 
  = ArgsMode          -- ^ searching for arguments of functions that can eventually 
                      --   produce the top level hole fill
  | ResultMode        -- ^ searching for the hole fill 
  deriving Eq 

genTerms' :: SearchMode -> String -> SpecType -> SM [CoreExpr] 
genTerms' i s specTy = 
  do  em    <- fixEMem specTy 
      fnTys <- functionCands (toType specTy)
      es    <- withTypeEs s specTy 
      filterElseM (hasType " genTerms " True specTy) es $ 
        withDepthFill i s specTy 0 [] fnTys

fixEMem :: SpecType -> SM ExprMemory
fixEMem t
  = do  sEMem <- sExprMem <$> get
        ts <- (snd . sForalls) <$> get
        fs <- (fst . sForalls) <$> get 
        let uTys = unifyWith (toType t)
        needsFix <- case find (\x -> x == uTys) ts of Nothing -> return True   -- not yet instantiated
                                                      Just _  -> return False  -- already instantiated
        let f = map (map showTy)
        if needsFix
          then do let es = map (\v -> instantiateTy (GHC.Var v) (Just uTys)) fs
                  modify (\s -> s { sForalls = (fs, uTys : ts)})
                  let notForall e = case exprType e of { ForAllTy{} -> False; _ -> True }
                  let fixEs = filter notForall es
                  thisDepth <- sDepth <$> get
                  let fixedEMem = (map (\e -> (exprType e, e, thisDepth + 1)) fixEs)
                  modify (\s -> s {sExprMem = fixedEMem ++ sExprMem s})
                  return (fixedEMem ++ sEMem) 
          else return sEMem
        

withDepthFill :: SearchMode -> String -> SpecType -> Int -> [(Symbol, (Type, Var))] -> [(Type, GHC.CoreExpr, Int)] -> SM [CoreExpr]
withDepthFill i s t depth funTyCands tmp = do
  let s0 = " [ withDepthFill ] " ++ s
  curEm <- sExprMem <$> get
  exprs <- fill i s0 depth curEm tmp []

  filterElseM (hasType s0 True t) exprs $ 
    if depth < maxAppDepth
      then withDepthFill i s0 t (depth + 1) funTyCands tmp
      else return []

fill :: SearchMode -> String -> Int -> ExprMemory -> [(Type, GHC.CoreExpr, Int)] -> [CoreExpr] -> SM [CoreExpr] 
fill i s _     _       []                 accExprs = return accExprs
fill i s depth exprMem (c@(t, e, d) : cs) accExprs = do
  let (resTy, subGs) = subgoals t
      argCands       = map (withSubgoal exprMem) subGs 
      changeMode     = foldr (\l b -> null l || b) False argCands

  curAppDepth <- sAppDepth <$> get 
  newExprs <- if i == ArgsMode || changeMode
                then do goals <- liftCG $ mapM trueTy subGs 
                        argCands0 <- mapM (genTerms' ArgsMode " | fill -> genTerms0 | ") goals
                        let argCands1 = map (map (, curAppDepth + 1)) argCands0
                        repeatPrune curAppDepth 1 (length argCands1) c argCands1 []
                else do curAppDepth <- sAppDepth <$> get 
                        repeatPrune curAppDepth 1 (length argCands) c argCands []
  let nextEm = map (resTy, , curAppDepth + 1) newExprs
  modify (\s -> s {sExprMem = nextEm ++ sExprMem s }) 
  let accExprs' = newExprs ++ accExprs
  fill i (" | " ++ show e ++ " FALSE CHECK | " ++ s) depth exprMem cs accExprs' 

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
repeatPrune :: Depth -> Up -> Down -> (Type, GHC.CoreExpr, Int) -> [[(CoreExpr, Int)]] -> [CoreExpr] -> SM [CoreExpr]
repeatPrune depth down up toBeFilled cands acc = 
  if down <= up 
    then do 
      let (cands', cands'') = updateIthElem down depth cands 
      es <- fillOne toBeFilled cands'
      acc' <- (++ acc) <$> filterM isWellTyped es
      repeatPrune depth (down + 1) up toBeFilled cands'' acc'
    else return acc


----------------------------------------------------------------------------
--  | Term generation: Perform type and term application for functions. | --
----------------------------------------------------------------------------

fillOne :: (Type, GHC.CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
fillOne (_, e, _)         [] = trace ( " [ fillOne ] " ++ show e) $ return [] -- TODO Fix it
fillOne (t, e, d) cs = applyTerms [e] cs (t0:ts)
  where (t0, ts) = safeSubgoals t

applyTerm :: [GHC.CoreExpr] -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyTerm es args t 
  = do  !idx <- incrSM 
        return  [ case e0 of  GHC.Var _ ->  GHC.App e e0
                              _         ->  
                                let letv = mkVar (Just "x") idx t
                                in  GHC.Let (GHC.NonRec letv e0) (GHC.App e (GHC.Var letv)) 
                | e <- es, (e0, _) <- args 
                ]

applyTerms :: [GHC.CoreExpr] -> [[(CoreExpr, Int)]] -> [Type] -> SM [CoreExpr]
applyTerms es []     []      
  = return es
applyTerms es0 (c:cs) (t:ts) 
  = do  es1 <- applyTerm es0 c t
        applyTerms es1 cs ts
applyTerms es cs ts 
  = error $ "[ applyTerms ] Wildcard. " 

--------------------------------------------------------------------------------------------

-- | @safeSubgoals@: For the input types of @t@, returns a tuple of 
--   the 1st input type and the rest input types.
--   @t@ is a function type. Otherwise, it throws an error.
safeSubgoals :: Type -> (Type, [Type])
safeSubgoals t = 
  case ts of  [ ]     -> error $ " [ safeSubgoals ] Should be a function type " ++ showTy t 
              t : ts' -> (t, ts') 
  where subgoals = createSubgoals t                    -- Includes the result type 
        ts       = take (length subgoals - 1) subgoals -- Input types from the subgoals

subgoals :: Type ->         -- ^ Given a function type,
            (Type, [Type])  -- ^ separate the result type from the input types.
subgoals t = (resTy, inpTys) where  gTys   = createSubgoals t 
                                    resTy  = last gTys 
                                    inpTys = take (length gTys - 1) gTys


-- @withSubgoal@ :: Takes a subgoal type, and 
-- returns all expressions in @ExprMemory@ that have the same type.
withSubgoal :: ExprMemory -> Type -> [(CoreExpr, Int)]
withSubgoal []                  _ = []
withSubgoal ((t, e, i) : exprs) τ = 
  if τ == t 
    then (e, i) : withSubgoal exprs τ
    else withSubgoal exprs τ

-- Misc : Move them 
getVn :: (Symbol, (Type, Var)) -> String 
getVn (_, (t, vn)) = "( " ++ show vn ++ ", " ++ showTy t ++ " )"

getVars0 :: [(Symbol, (Type, Var))] -> [Var] 
getVars0 []                 = []
getVars0 ((_, (_, v)) : vs) = v : getVars0 vs

getExprs0 :: ExprMemory -> [GHC.CoreExpr]
getExprs0 []             = []
getExprs0 ((_, e, _):es) = e : getExprs0 es
