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
  do  fixEMem specTy 
      fnTys <- functionCands (toType specTy)
      es    <- withTypeEs s specTy 
      filterElseM (hasType " genTerms " True specTy) es $ 
        withDepthFill i s specTy 0 (tracepp " Candidates " fnTys)

nonTrivial :: GHC.CoreExpr -> Bool
-- TODO: e should not be a nullary constructor
nonTrivial (GHC.App e (GHC.Type _)) = False
nonTrivial _                        = True

nonTrivials :: [GHC.CoreExpr] -> Bool
nonTrivials = foldr (\x b -> nonTrivial x || b) False 

trivial :: GHC.CoreExpr -> Bool
trivial (GHC.App (GHC.Var _) (GHC.Type _)) = True -- Is this a nullary constructor?
trivial _ = False

hasTrivial :: [GHC.CoreExpr] -> Bool
hasTrivial es = foldr (\x b -> trivial x || b) False es

allTrivial :: [[GHC.CoreExpr]] -> Bool
allTrivial es = foldr (\x b -> hasTrivial x && b) True es 

rmTrivials :: [(GHC.CoreExpr, Int)] -> [(GHC.CoreExpr, Int)]
rmTrivials = filter (\x -> not (trivial (fst x))) 



fixEMem :: SpecType -> SM ()
fixEMem t
  = do  (fs, ts) <- sForalls <$> get
        let uTys = unifyWith (toType t)
        needsFix <- case find (== uTys) ts of Nothing -> return True   -- not yet instantiated
                                              Just _  -> return False  -- already instantiated

        when needsFix $
          do  modify (\s -> s { sForalls = (fs, uTys : ts)})
              let notForall e = case exprType e of { ForAllTy{} -> False; _ -> True }
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
    filterElseM (hasType s0 True t) (notrace " [ Expressions ] " exprs) $ 
      if depth < maxAppDepth
        then withDepthFill i s0 t (depth + 1) tmp
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
                                  argCands0 <- mapM (genTerms' ArgsMode " | fill ArgsMode | ") goals
                                  let argCands2 = map (map (, curAppDepth + 1)) argCands0
                                      argCands1 = if allTrivial (map (map fst) argCands2) 
                                                    then map rmTrivials argCands2
                                                    else argCands2
                                  repeatPrune curAppDepth 1 (length argCands1) c argCands1 []
                          else do curAppDepth <- sAppDepth <$> get 
                                  repeatPrune curAppDepth 1 (length argCands) c argCands []
            let nextEm = map (resTy, , curAppDepth + 1) newExprs
            trace (" next " ++ show (map snd3 nextEm)) $ modify (\s -> s {sExprMem = nextEm ++ sExprMem s }) 
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
fillOne (_, e, _) [] 
  = {- trace ( " [ fillOne ] " ++ show e) $ -} return []  -- TODO Fix it: Shouldn't be called 
                                                          -- if cs is empty
fillOne (t, e, d) cs 
  = applyTerms [e] cs ((snd . fromJust . subgoals) t)     -- TODO Fix fromJust 

applyTerm :: [GHC.CoreExpr] -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyTerm es args t 
  = do  !idx <- incrSM 
        return  [ case e0 of  GHC.Var _ ->  GHC.App e e0
                              _         ->  let letv = mkVar (Just "x") idx t
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