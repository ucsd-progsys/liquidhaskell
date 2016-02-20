{-# LANGUAGE PatternGuards    #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

--------------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ---------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Solve (solve, gradualSolve ) where

import           Control.Monad (filterM)
import           Control.Monad.State.Strict (lift)
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (stats)
import qualified Language.Fixpoint.Solver.Solution as S
import qualified Language.Fixpoint.Solver.Worklist as W
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Solver.Graph (isTarget)
import           Text.PrettyPrint.HughesPJ

-- DEBUG
import           Text.Printf
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Control.DeepSeq

import           Data.List  (sort)
import           Data.Maybe (catMaybes)
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
solve :: (NFData a, F.Fixpoint a) => Config -> F.Solution -> F.SInfo a -> IO (F.Result (Integer, a))
--------------------------------------------------------------------------------
solve cfg s0 fi = do
    -- donePhase Loud "Worklist Initialize"
    (res, stat) <- runSolverM cfg fi n act
    whenLoud $ printStats fi wkl stat
    -- print (numIter stat)
    return res
  where
    wkl  = W.init fi
    n    = fromIntegral $ W.wRanks wkl
    act  = solve_ cfg fi s0 wkl

printStats :: F.SInfo a ->  W.Worklist a -> Stats -> IO ()
printStats fi w s = putStrLn "\n" >> ppTs [ ptable fi, ptable s, ptable w ]
  where
    ppTs          = putStrLn . showpp . mconcat


--------------------------------------------------------------------------------
solve_ :: (NFData a, F.Fixpoint a)
       => Config -> F.SInfo a -> F.Solution -> W.Worklist a
       -> SolveM (F.Result (Integer, a), Stats)
--------------------------------------------------------------------------------
solve_ cfg fi s0 wkl = do
  let s0'  = mappend s0 $ {-# SCC "sol-init" #-} S.init fi
  s       <- {-# SCC "sol-refine" #-} refine s0' wkl
  st      <- stats
  res     <- {-# SCC "sol-result" #-} result cfg wkl s
  let res' = {-# SCC "sol-tidy"   #-} tidyResult res
  return $!! (res', st)

-- | tidyResult ensures we replace the temporary kVarArg names
--   introduced to ensure uniqueness with the original names
--   appearing in the supplied WF constraints.

tidyResult :: F.Result a -> F.Result a
tidyResult r = r { F.resSolution = tidySolution (F.resSolution r) }

tidySolution :: F.FixSolution -> F.FixSolution
tidySolution = fmap tidyPred

tidyPred :: F.Expr -> F.Expr
tidyPred = F.substf (F.eVar . F.tidySymbol)

--------------------------------------------------------------------------------
refine :: F.Solution -> W.Worklist a -> SolveM F.Solution
--------------------------------------------------------------------------------
refine s w
  | Just (c, w', newScc, rnk) <- W.pop w = do
     i       <- tickIter newScc
     (b, s') <- refineC i s c
     lift $ writeLoud $ refineMsg i c b rnk
     let w'' = if b then W.push c w' else w'
     refine s' w''
  | otherwise = return s

-- DEBUG
refineMsg i c b rnk = printf "\niter=%d id=%d change=%s rank=%d\n"
                        i (F.subcId c) (show b) rnk

---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: Int -> F.Solution -> F.SimpC a -> SolveM (Bool, F.Solution)
---------------------------------------------------------------------------
refineC _i s c
  | null rhs  = return (False, s)
  | otherwise = do be     <- getBinds
                   let lhs = S.lhsPred be s c
                   kqs    <- filterValid lhs rhs
                   return  $ S.update s ks {- tracepp (msg ks rhs kqs) -} kqs
  where
    (ks, rhs) = rhsCands s c
    -- msg ks xs ys = printf "refineC: iter = %d, ks = %s, rhs = %d, rhs' = %d \n" _i (showpp ks) (length xs) (length ys)

rhsCands :: F.Solution -> F.SimpC a -> ([F.KVar], F.Cand (F.KVar, F.EQual))
rhsCands s c   = (fst <$> ks, kqs)
  where
    kqs        = [ cnd k su q | (k, su) <- ks, q <- F.solLookup s k]
    ks         = predKs . F.crhs $ c
    cnd k su q = (F.subst su (F.eqPred q), (k, q))

predKs :: F.Expr -> [(F.KVar, F.Subst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k su) = [(k, su)]
predKs _              = []

---------------------------------------------------------------------------
-- | Convert Solution into Result -----------------------------------------
---------------------------------------------------------------------------
result :: (F.Fixpoint a) => Config -> W.Worklist a -> F.Solution -> SolveM (F.Result (Integer, a))
---------------------------------------------------------------------------
result _ wkl s = do
  lift $ writeLoud "Computing Result"
  stat    <- result_ wkl s
  -- stat'   <- gradualSolve cfg stat
  lift $ print (F.sid <$> stat)
  return   $ F.Result (ci <$> stat) (F.solResult s)
  where
    ci c = (F.subcId c, F.sinfo c)


result_ :: W.Worklist a -> F.Solution -> SolveM (F.FixResult (F.SimpC a))
result_  w s = res <$> filterM (isUnsat s) cs
  where
    cs       = W.unsatCandidates w
    res []   = F.Safe
    res cs'  = F.Unsafe cs'

---------------------------------------------------------------------------
isUnsat :: F.Solution -> F.SimpC a -> SolveM Bool
---------------------------------------------------------------------------
isUnsat s c = do
  be    <- getBinds
  let lp = S.lhsPred be s c
  let rp = rhsPred        c
  res   <- not <$> isValid lp rp
  lift   $ whenLoud $ showUnsat res (F.subcId c) lp rp
  return res

showUnsat :: Bool -> Integer -> F.Pred -> F.Pred -> IO ()
showUnsat u i lP rP = {- when u $ -} do
  putStrLn $ printf   "UNSAT id %s %s" (show i) (show u)
  putStrLn $ showpp $ "LHS:" <+> pprint lP
  putStrLn $ showpp $ "RHS:" <+> pprint rP



--------------------------------------------------------------------------------
-- | Predicate corresponding to RHS of constraint in current solution
--------------------------------------------------------------------------------
rhsPred :: F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
rhsPred c
  | isTarget c = F.crhs c
  | otherwise  = errorstar $ "rhsPred on non-target: " ++ show (F.sid c)

isValid :: F.Expr -> F.Expr -> SolveM Bool
isValid p q = (not . null) <$> filterValid p [(q, ())]



--------------------------------------------------------------------------------
-- | RJ: @nikivazou please add some description here of what this does.
--------------------------------------------------------------------------------
gradualSolve :: (Fixpoint a)
             => Config
             -> F.FixResult (F.SimpC a)
             -> SolveM (F.FixResult (F.SimpC a))
gradualSolve cfg (F.Unsafe cs)
  | gradual cfg   = go cs
  where
    go cs         = smtEnablrmbqi >> (makeResult . catMaybes <$> mapM gradualSolveOne cs)
    makeResult    = applyNonNull F.Safe F.Unsafe
gradualSolve _  r = return r

gradualSolveOne :: (F.Fixpoint a) => F.SimpC a -> SolveM (Maybe (F.SimpC a))
gradualSolveOne c =
  do γ0 <- makeEnvironment c
     let (γ, γ', hasGradual) = splitLastGradual γ0
     if hasGradual
      then do let vc = makeGradualExpression γ γ' (F.crhs c)
              s <- checkSat vc
              return {- traceShow ("DEBUG" ++ show  (γ, γ', F.crhs c) ++ "\nVC = \n" ++ show (vc, s) ) -}
                 $ if s then Nothing else Just c
      else return $ Just c

makeGradualExpression γ γ' p
  = F.PAnd [F.PAll bs (F.PImp gs p), gs]
  where
    bs = [ (x, s) | (x, F.RR s _) <- γ']
    gs = F.pAnd (bindToLogic <$> (γ ++ γ'))
    bindToLogic (x, F.RR _ (F.Reft (v, e))) = e `F.subst1` (v, F.EVar x)

makeEnvironment  c
  = do lp <- getBinds
       return [ F.lookupBindEnv i lp | i <- bs ]
  where
    bs = sort $ F.elemsIBindEnv $ F.senv c

splitLastGradual = go [] . reverse
  where
    go acc (xe@(x, F.RR s (F.Reft (v, e))) : xss)
      | Just es <- removePGrads e
      = (reverse ((x, F.RR s (F.Reft (v, F.pAnd es))):xss), reverse acc, True)
      | otherwise
      = go (xe:acc) xss
    go acc []
      = ([], reverse acc, False)

removePGrads (F.PAnd es)
  | F.PGrad `elem` es
  = Just $ filter (/= F.PGrad) es
  | otherwise
  = Nothing
removePGrads F.PGrad
  = Just []
removePGrads _
  = Nothing

{-
---------------------------------------------------------------------------
donePhase' :: String -> SolveM ()
---------------------------------------------------------------------------
donePhase' msg = lift $ do
  threadDelay 25000
  putBlankLn
  donePhase Loud msg
-}
