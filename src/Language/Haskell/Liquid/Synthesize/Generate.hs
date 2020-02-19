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
 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Fixpoint.Types.PrettyPrint
import           Debug.Trace 
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)
import           Data.Tuple.Extra 
import           Data.List 

import           MkCore
import           DynFlags

-- Generate terms that have type t: This changes the @ExprMemory@ in @SM@ state.
-- Return expressions type checked against type @specTy@.
genTerms :: String -> SpecType -> SM [CoreExpr] 
genTerms = genTerms' ResultMode 


data SearchMode 
  = ArgsMode          -- ^ searching for arguments of functions that can eventually 
                      --   produce the top level hole fill
  | ResultMode        -- ^ searching for the hole fill 
  deriving (Eq, Show) 

genTerms' :: SearchMode -> String -> SpecType -> SM [CoreExpr] 
genTerms' i s specTy = 
  do  fixEMem specTy 
      fnTys <- functionCands (toType specTy)
      es    <- withTypeEs s specTy 
      err <- checkError specTy 
      case err of 
        Nothing ->
          filterElseM (hasType " genTerms " True specTy) es $ 
            withDepthFill i s specTy 0 fnTys
        Just e -> return [e]

checkError :: SpecType -> SM (Maybe CoreExpr)
checkError t = do 
  errVar <- varError
  let errorExpr = GHC.App (GHC.App (GHC.Var errVar) (GHC.Type (toType t))) errorInt
      errorInt  = mkIntExprInt unsafeGlobalDynFlags 42
  b <- hasType " checkError " True t errorExpr
  if b 
    then return $ Just errorExpr
    else return Nothing

fixEMem :: SpecType -> SM ()
fixEMem t
  = do  (fs, ts) <- sForalls <$> get
        let uTys = unifyWith (toType t)
        needsFix <- case find (== uTys) ts of 
                      Nothing -> return True   -- not yet instantiated
                      Just _  -> return False  -- already instantiated

        when needsFix $
          do  modify (\s -> s { sForalls = (fs, uTys : ts)})
              let notForall e = case exprType e of {ForAllTy{} -> False; _ -> True}
                  es = map (\v -> instantiateTy (GHC.Var v) (Just uTys)) fs
                  fixEs = filter notForall es
              thisDepth <- sDepth <$> get
              let fixedEMem = map (\e -> (exprType e, e, thisDepth + 1)) fixEs
              modify (\s -> s {sExprMem = fixedEMem ++ sExprMem s})

withDepthFill :: SearchMode -> String -> SpecType -> Int -> [(Type, GHC.CoreExpr, Int)] -> SM [CoreExpr]
withDepthFill i s t depth tmp = do
  let s0 = " [ withDepthFill ] " ++ s
  curEm <- sExprMem <$> get
  exprs <- fill i s0 depth curEm tmp []

  if nonTrivials exprs then 
    filterElseM (hasType s0 True t) exprs $ 
      if depth < maxAppDepth
        then do modify (\s -> s { sAppDepth = sAppDepth s + 1 })
                withDepthFill i s0 t (depth + 1) tmp
        else return []
    else return []

fill :: SearchMode -> String -> Int -> ExprMemory -> [(Type, GHC.CoreExpr, Int)] -> [CoreExpr] -> SM [CoreExpr] 
fill _ _ _     _       []                 accExprs 
  = return accExprs
fill i s depth exprMem (c@(t, e, d) : cs) accExprs 
  = case subgoals t of 
      Nothing             -> return [] -- Not a function type
      Just (resTy, subGs) ->          
        do  let argCands'  = map (withSubgoal exprMem) subGs 
                argCands   = if allTrivial (map (map fst) argCands')
                              then map rmTrivials argCands'
                              else argCands'
                changeMode = foldr (\l b -> null l || b) False argCands
            curAppDepth <- sAppDepth <$> get 
            newExprs <- if i == ArgsMode || changeMode
                          then do goals <- liftCG $ mapM trueTy subGs 
                                  argCands0 <- mapM (genTerms' ArgsMode " fill Args ") goals
                                  let argCands2 = map (map (, curAppDepth + 1)) argCands0
                                      argCands1 = if allTrivial (map (map fst) argCands2) 
                                                    then map rmTrivials argCands2
                                                    else argCands2
                                  prune curAppDepth c argCands1
                          else do curAppDepth <- sAppDepth <$> get 
                                  prune curAppDepth c argCands
            let nextEm = map (resTy, , curAppDepth + 1) newExprs
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s }) 
            em <- sExprMem <$> get
            let accExprs' = newExprs ++ accExprs
            fill i (" | " ++ show e ++ " FALSE CHECK | " ++ s) depth em cs accExprs' 

-------------------------------------------------------------------------------------------
-- |                       Pruning terms for function application                      | --
-------------------------------------------------------------------------------------------
type Depth = Int

feasible :: Depth -> (CoreExpr, Int) -> Bool
feasible d c = snd c >= d

feasibles :: Depth -> Int -> [(CoreExpr, Int)] -> [Int]
feasibles _ _ []
  = []
feasibles d i (c:cs) 
  = if feasible d c 
      then i : feasibles d (i+1) cs
      else feasibles d (i+1) cs

isFeasible :: Depth -> [[(CoreExpr, Int)]] -> [[Int]]
isFeasible _ []
  = []
isFeasible d (c:cs) 
  =  if null fs 
      then [] : isFeasible d cs
      else fs : isFeasible d cs
      where fs = feasibles d 0 c

toIxs :: Int -> [[Int]] -> [Int]
toIxs _ [] 
  = [] 
toIxs i (f:fs)
  = if null f 
      then toIxs (i+1) fs
      else i : toIxs (i+1) fs

findFeasibles :: Depth -> [[(CoreExpr, Int)]] -> ([[Int]], [Int])
findFeasibles d cs = (fs, ixs)
  where fs  = isFeasible d cs
        ixs = toIxs 0 fs

toExpr :: Int ->                      -- ^ Reference index. Starting from 0.
          [Int] ->                    -- ^ Produced from @isFeasible@.
                                      --   Assumed in increasing order.
          [(GHC.CoreExpr, Int)] ->    -- ^ The candidate expressions.
          ([(GHC.CoreExpr, Int)],     -- ^ Expressions from 2nd argument.
           [(GHC.CoreExpr, Int)]) ->  -- ^ The rest of the expressions
          ([(GHC.CoreExpr, Int)], [(GHC.CoreExpr, Int)])
toExpr _  []     _    res
  = res 
toExpr ix (i:is) args (b, nb) = 
  if ix == i 
    then toExpr (ix+1) is args (args!!i : b, nb)
    else toExpr (ix+1) is args (b, args !! i : nb)


fixCands :: Int -> [Int] -> [[(CoreExpr, Int)]] -> ([[(CoreExpr, Int)]], [[(CoreExpr, Int)]])
fixCands i ixs args 
  = let cs = args !! i
        (cur, next) = toExpr 0 ixs cs ([], [])
        (args0, args1) = (replace (i+1) cur args, replace (i+1) next args)
    in  (args0, args1)

-- | The first argument should be an 1-based index.
replace :: Int -> a -> [a] -> [a]
replace i x l
  = left ++ [x] ++ right
    where left  = take (i-1) l
          right = drop i l

repeatFix :: [Int] -> [[Int]] -> (Type, CoreExpr, Int) -> [[(CoreExpr, Int)]] -> [CoreExpr] -> SM [CoreExpr]
repeatFix [ ] _ _ _ es 
  = return es
repeatFix (i:is) ixs toFill args es
  = do  let (args0, args1) = fixCands i (ixs !! i) args
        es0 <- fillOne toFill args0
        es1 <- (++ es) <$> filterM isWellTyped es0
        repeatFix is ixs toFill args1 es1

prune :: Depth -> (Type, CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
prune d toFill args 
  = do  let (ixs, is) = findFeasibles d args 
        repeatFix is ixs toFill args []


----------------------------------------------------------------------------
--  | Term generation: Perform type and term application for functions. | --
----------------------------------------------------------------------------

fillOne :: (Type, GHC.CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
fillOne (_, e, _) [] 
  = {- trace ( " [ fillOne ] " ++ show e) $ -} return []  -- TODO Fix it: Shouldn't be called 
                                                          -- if cs is empty
fillOne (t, e, d) cs 
  = applyTerms [e] cs ((snd . fromJust . subgoals) t)     -- TODO Fix fromJust 

applyTerm :: [GHC.CoreExpr] -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyTerm es args t = do
  es1 <- mapM (\x -> applyArg es x t) args
  return (concat es1)

applyArg :: [GHC.CoreExpr] -> (CoreExpr, Int) -> Type -> SM [CoreExpr]
applyArg es (arg, _) t 
  = do  !idx <- incrSM
        return  [ case arg of GHC.Var _ -> GHC.App e arg
                              _         ->  let letv = mkVar (Just ("x" ++ show idx)) idx t
                                            in  GHC.Let (GHC.NonRec letv arg) (GHC.App e (GHC.Var letv))
                | e <- es 
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

subgoals :: Type ->               -- ^ Given a function type,
            Maybe (Type, [Type])  -- ^ separate the result type from the input types.
subgoals t = if null gTys then Nothing else Just (resTy, inpTys) 
  where gTys            = createSubgoals t 
        (resTy, inpTys) = (last gTys, take (length gTys - 1) gTys)


-- @withSubgoal@ :: Takes a subgoal type, and 
-- returns all expressions in @ExprMemory@ that have the same type.
withSubgoal :: ExprMemory -> Type -> [(CoreExpr, Int)]
withSubgoal []                  _ = []
withSubgoal ((t, e, i) : exprs) τ = 
  if τ == t 
    then (e, i) : withSubgoal exprs τ
    else withSubgoal exprs τ

--------------------------------------------------------------------------------------------