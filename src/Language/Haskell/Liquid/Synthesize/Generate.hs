{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Generate where

import           Language.Haskell.Liquid.GHC.API as GHC hiding (Depth)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Synthesize.GHC
                                         hiding ( SSEnv )
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc
                                         hiding ( notrace )
import           Language.Haskell.Liquid.Synthesize.Check
import           Data.Maybe
import           Control.Monad.State.Lazy
import           Language.Haskell.Liquid.Constraint.Fresh
                                                ( trueTy )
import           Data.List
import           Data.Tuple.Extra
import           Language.Fixpoint.Types.PrettyPrint (tracepp)

-- Generate terms that have type t: This changes the @ExprMemory@ in @SM@ state.
-- Return expressions type checked against type @specTy@.
genTerms :: SpecType -> SM [CoreExpr] 
genTerms = genTerms' ResultMode 


data SearchMode 
  = ArgsMode          -- ^ searching for arguments of functions that can eventually 
                      --   produce the top level hole fill
  | ResultMode        -- ^ searching for the hole fill 
  deriving (Eq, Show) 

genTerms' :: SearchMode -> SpecType -> SM [CoreExpr] 
genTerms' i specTy = 
  do  goalTys <- sGoalTys <$> get
      case find (== toType False specTy) goalTys of 
        Nothing -> modify (\s -> s { sGoalTys = (toType False specTy) : sGoalTys s })
        Just _  -> return ()
      fixEMem specTy 
      fnTys <- functionCands (toType False specTy)
      es    <- withTypeEs specTy 
      es0   <- structuralCheck es

      err <- checkError specTy 
      case err of 
        Nothing ->
          filterElseM (hasType specTy) es0 $ 
            withDepthFill i specTy 0 fnTys
        Just e -> return [e]

genArgs :: SpecType -> SM [CoreExpr]
genArgs t =
  do  goalTys <- sGoalTys <$> get
      case find (== toType False t) goalTys of 
        Nothing -> do modify (\s -> s { sGoalTys = toType False t : sGoalTys s }) 
                      fixEMem t 
                      fnTys <- functionCands (toType False t)
                      es <- withDepthFillArgs t 0 fnTys
                      if null es
                        then  return []
                        else  do  -- modify (\s -> s {sExprId = sExprId s + 1})
                                  return es
        Just _  -> return []

withDepthFillArgs :: SpecType -> Int -> [(Type, CoreExpr, Int)] -> SM [CoreExpr]
withDepthFillArgs t depth cs = do
  thisEm <- sExprMem <$> get
  es <- argsFill thisEm cs []
  argsDepth <- localMaxArgsDepth

  filterElseM (hasType t) es $
    if depth < argsDepth
      then  trace (" [ withDepthFillArgs ] argsDepth = " ++ show argsDepth) $ withDepthFillArgs t (depth + 1) cs
      else  return []

argsFill :: ExprMemory -> [(Type, CoreExpr, Int)] -> [CoreExpr] -> SM [CoreExpr]
argsFill _   []               es0 = return es0 
argsFill em0 (c:cs) es0 =
  case subgoals (fst3 c) of
    Nothing             -> return [] 
    Just (resTy, subGs) -> 
      do  let argCands = map (withSubgoal em0) subGs
              toGen    = foldr (\x b -> (not . null) x && b) True (tracepp (" [ argsFill ] for c = " ++ show (snd3 c) ++ " argCands ") argCands)
          es <- do  curExprId <- sExprId <$> get
                    if toGen then 
                      prune curExprId c argCands
                      else return []
          curExprId <- sExprId <$> get
          let nextEm = map (resTy, , curExprId + 1) es
          modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
          argsFill em0 cs (es ++ es0)

withDepthFill :: SearchMode -> SpecType -> Int -> [(Type, GHC.CoreExpr, Int)] -> SM [CoreExpr]
withDepthFill i t depth tmp = do
  exprs <- fill i depth tmp []
  appDepth <- localMaxAppDepth

  filterElseM (hasType t) exprs $ 
      if depth < appDepth
        then do modify (\s -> s { sExprId = sExprId s + 1 })
                withDepthFill i t (depth + 1) tmp
        else return []

fill :: SearchMode -> Int -> [(Type, GHC.CoreExpr, Int)] -> [CoreExpr] -> SM [CoreExpr] 
fill _ _     []                 accExprs 
  = return accExprs
fill i depth (c : cs) accExprs 
  = case subgoals (fst3 c) of 
      Nothing             -> return [] -- Not a function type
      Just (resTy, subGs) ->
        do  specSubGs <- liftCG $ mapM (trueTy False) (filter (not . isFunction) subGs)
            mapM_ genArgs specSubGs
            em <- sExprMem <$> get
            let argCands  = map (withSubgoal em) subGs
                toGen    = foldr (\x b -> (not . null) x && b) True argCands
            newExprs <- do  curExprId <- sExprId <$> get 
                            if toGen 
                              then prune curExprId c (tracepp (" [ fill " ++ show curExprId ++ " ] For c = " ++ show (snd3 c) ++ " argCands ") argCands)
                              else return []
            curExprId <- sExprId <$> get
            let nextEm = map (resTy, , curExprId + 1) newExprs
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s }) 
            let accExprs' = newExprs ++ accExprs
            fill i depth cs accExprs' 

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
isFeasible d =  map (feasibles d 0)

findFeasibles :: Depth -> [[(CoreExpr, Int)]] -> ([[Int]], [Int])
findFeasibles d cs = (fs, ixs)
  where fs  = isFeasible d cs
        ixs = [i | (i, f) <- zip [0..] fs, not (null f)]

toExpr :: [Int] ->                    --  Produced from @isFeasible@.
                                      --   Assumed in increasing order.
          [(GHC.CoreExpr, Int)] ->    --  The candidate expressions.
          ([(GHC.CoreExpr, Int)],     --  Expressions from 2nd argument.
           [(GHC.CoreExpr, Int)])     --  The rest of the expressions
toExpr ixs args = ( [ args !! i | (ix, i) <- is, ix == i ], 
                    [ args !! i | (ix, i) <- is, ix /= i ])
    where is = zip [0..] ixs

fixCands :: Int -> [Int] -> [[(CoreExpr, Int)]] -> ([[(CoreExpr, Int)]], [[(CoreExpr, Int)]])
fixCands i ixs args 
  = let cs = args !! i
        (cur, next)    = toExpr ixs cs
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
        es1 <- structuralCheck es0
        es2 <- (++ es) <$> filterM isWellTyped es1
        repeatFix is ixs toFill args1 es2

prune :: Depth -> (Type, CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
prune d toFill args 
  = do  let (ixs, is) = findFeasibles d args 
        repeatFix is ixs toFill args []


----------------------------------------------------------------------------
--  | Term generation: Perform type and term application for functions. | --
----------------------------------------------------------------------------

fillOne :: (Type, GHC.CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
fillOne _ [] 
  = return []
fillOne (t, e, _) cs 
  = applyTerms [e] cs ((snd . fromJust . subgoals) t)

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
applyTerms _es _cs _ts 
  = error "[ applyTerms ] Wildcard. " 

--------------------------------------------------------------------------------------
prodScrutinees :: [(Type, CoreExpr, Int)] -> [[[(CoreExpr, Int)]]] -> SM [CoreExpr]
prodScrutinees []     []     = return []
prodScrutinees (c:cs) (a:as) = do 
  es <- fillOne c a
  (++ es) <$> prodScrutinees cs as
prodScrutinees _ _ = error " prodScrutinees "

synthesizeScrutinee :: [Var] -> SM [CoreExpr]
synthesizeScrutinee vars = do
  s <- get
  let foralls = (fst . sForalls) s
      insVs = sUniVars s
      fix'  = sFix s
      -- Assign higher priority to function candidates that return tuples
      fnCs0 = filter returnsTuple foralls 
      fnCs  = if returnsTuple fix' then fix' : fnCs0 else fnCs0

      fnEs  = map GHC.Var fnCs
      fnCs' = map (\e -> instantiate e (Just insVs)) fnEs
      sGs   = map ((snd . fromJust) . subgoals . exprType) fnCs'
      argCands = map (map (withSubgoal vs)) sGs
      fnCs'' = map (\e -> (exprType e, e, 0)) fnCs'
      
      vs' = filter ((not . isFunction) . varType) vars
      vs  = map (\v -> (varType v, GHC.Var v, 0)) vs'
  prodScrutinees fnCs'' argCands
