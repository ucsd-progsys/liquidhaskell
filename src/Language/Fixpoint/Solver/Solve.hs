{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns      #-}

--------------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ---------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Solve (solve, gradualSolve ) where

import           Control.Monad (when, filterM, foldM)
import           Control.Monad.State.Strict (lift)
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types           as F
import qualified Language.Fixpoint.Types.Solutions as Sol
import qualified Language.Fixpoint.SortCheck       as So
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (stats)
import qualified Language.Fixpoint.Solver.Solution  as S
import qualified Language.Fixpoint.Solver.Worklist  as W
import qualified Language.Fixpoint.Solver.Eliminate as E
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Graph
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
import           System.Console.CmdArgs.Verbosity (whenNormal, whenLoud)
import           Control.DeepSeq
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

-- DEBUG
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
solve :: (NFData a, F.Fixpoint a) => Config -> F.SInfo a -> IO (F.Result (Integer, a))
--------------------------------------------------------------------------------
solve cfg fi = do
    -- donePhase Loud "Worklist Initialize"
    (res, stat) <- withProgressFI sI $ runSolverM cfg sI n act
    when (solverStats cfg) $ printStats fi wkl stat
    -- print (numIter stat)
    return res
  where
    act  = solve_ cfg fi s0 ks  wkl
    sI   = solverInfo cfg fi
    wkl  = W.init sI
    n    = fromIntegral $ W.wRanks wkl
    s0   = siSol  sI
    ks   = siVars sI

--------------------------------------------------------------------------------
-- | Progress Bar
--------------------------------------------------------------------------------
withProgressFI :: SolverInfo a -> IO b -> IO b
withProgressFI = withProgress . fromIntegral . cNumScc . siDeps
--------------------------------------------------------------------------------

printStats :: F.SInfo a ->  W.Worklist a -> Stats -> IO ()
printStats fi w s = putStrLn "\n" >> ppTs [ ptable fi, ptable s, ptable w ]
  where
    ppTs          = putStrLn . showpp . mconcat

--------------------------------------------------------------------------------
solverInfo :: Config -> F.SInfo a -> SolverInfo a
--------------------------------------------------------------------------------
solverInfo cfg fI
  | useElim cfg = E.solverInfo cfg fI
  | otherwise   = SI mempty fI cD (siKvars fI)
  where
    cD          = elimDeps fI (kvEdges fI) mempty

siKvars :: F.SInfo a -> S.HashSet F.KVar
siKvars = S.fromList . M.keys . F.ws


--------------------------------------------------------------------------------
solve_ :: (NFData a, F.Fixpoint a)
       => Config
       -> F.SInfo a
       -> Sol.Solution
       -> S.HashSet F.KVar
       -> W.Worklist a
       -> SolveM (F.Result (Integer, a), Stats)
--------------------------------------------------------------------------------
solve_ cfg fi s0 ks wkl = do
  -- lift $ dumpSolution "solve_.s0" s0
  let s1  = mappend s0 $ {-# SCC "sol-init" #-} S.init cfg fi ks
  s2      <- {-# SCC "sol-grad-local" #-} filterLocal (traceShow "INIT SOL" s1) 
  s       <- {-# SCC "sol-refine" #-} refine  (traceShow "EDITED SOL" s2) wkl
  res     <- {-# SCC "sol-result" #-} result cfg wkl (traceShow "FINAL SOL" s)
  st      <- stats
  let res' = {-# SCC "sol-tidy"   #-} tidyResult res
  return $!! (res', st)

--------------------------------------------------------------------------------
-- | tidyResult ensures we replace the temporary kVarArg names introduced to
--   ensure uniqueness with the original names in the given WF constraints.
--------------------------------------------------------------------------------
tidyResult :: F.Result a -> F.Result a
tidyResult r = r { F.resSolution = tidySolution (F.resSolution r) }

tidySolution :: F.FixSolution -> F.FixSolution
tidySolution = fmap tidyPred

tidyPred :: F.Expr -> F.Expr
tidyPred = F.substf (F.eVar . F.tidySymbol)


filterLocal :: Sol.Solution -> SolveM Sol.Solution 
filterLocal !sol = do 
  gs' <- mapM (initGBind sol) gs 
  return $ Sol.updateGMap sol $ M.fromList gs'
  where 
    gs = M.toList $ Sol.gMap sol 

initGBind :: Sol.Solution -> (F.KVar, (((F.Symbol, F.Sort), F.Expr), Sol.GBind)) -> SolveM (F.KVar, (((F.Symbol, F.Sort), F.Expr), Sol.GBind))
initGBind sol (k, (e, gb)) = ((k,) . (e,) . Sol.equalsGb) <$> ( 
   filterM (isLocal e) ([Sol.trueEqual]:Sol.gbEquals gb)
   >>= \elems -> makeLattice 1 [] (traceShow "\nSTEP 0 :: \n" elems) (head <$> elems))  -- go [] (Sol.gbEquals gb) -- Sol.gbFilterM (isLocal e) gb 
  where
    makeLattice i acc new elems
      | null new
      = return acc 
      | otherwise
      = do let cands = [e:es |e<-elems, es <- new]
           localCans <- filterM (isLocal e) cands
           newElems  <- filterM (notTrivial (new ++ acc)) localCans 
           makeLattice (i+1) (acc ++ new) (traceShow ("\nSTEP " ++ show i ++ ":: \n") newElems) elems

    notTrivial [] _     = return True 
    notTrivial (x:xs) p = do v <- isValid (mkPred x) (mkPred p)
                             if v then return $ traceShow ("\nREJECT P " ++ showpp (mkPred p) ++ " FROM " ++  showpp (mkPred x)) False 
                                  else notTrivial xs p 

    mkPred eq = So.elaborate "initBGind.mkPred" (Sol.sEnv sol) (F.pAnd (Sol.eqPred <$> eq))

    -- local e eqs <=> \exists v . 
    isLocal (v, e) eqs = do 
      let pp = So.elaborate "filterLocal" (Sol.sEnv sol) $ F.PExist [v] $ F.pAnd (e:(Sol.eqPred <$> eqs)) 
      v <- isValid mempty pp --  errorstar ("\nSOL = \n" ++ "\nIs local " ++ (showpp $ pp))
      return $ traceShowp (show v ++ "isLocal CHECKED FOR " ++ showpp eqs ++ "\nPRED = \n" ++ showpp pp) v

traceShowp :: Show a => String -> a -> a 
traceShowp !str e = traceShow str e 

--------------------------------------------------------------------------------
refine :: Sol.Solution -> W.Worklist a -> SolveM Sol.Solution
--------------------------------------------------------------------------------
refine !s w
  | Just (c, w', newScc, rnk) <- W.pop w = do
     i       <- tickIter newScc
     (b, s') <- refineC i s c
     lift $ writeLoud $ refineMsg i c b rnk
     let w'' = if b then W.push c w' else w'
     refine s' w''
  | otherwise = return s
  where
    -- DEBUG
    refineMsg i c b rnk = printf "\niter=%d id=%d change=%s rank=%d\n"
                            i (F.subcId c) (show b) rnk

---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: Int -> Sol.Solution -> F.SimpC a -> SolveM (Bool, Sol.Solution)
---------------------------------------------------------------------------
refineC _i s c
  | null rhs  = return (False, s)
  | otherwise = do be     <- getBinds
                   let lhs = F.notracepp ("LHS at " ++ show _i) $ S.lhsPred be s c
                   kqs    <- filterValid lhs rhs
                   return  $ S.update s ks $ traceShow ("VALID KS = ") kqs
  where
    _ci       = F.subcId c
    (ks, rhs) = rhsCands s c
    -- msg       = printf "refineC: iter = %d, sid = %s, soln = \n%s\n"
    --               _i (show (F.sid c)) (showpp s)
    _msg ks xs ys = printf "refineC: iter = %d, sid = %s, s = %s, rhs = %d, rhs' = %d \n"
                     _i (show _ci) (showpp ks) (length xs) (length ys)

rhsCands :: Sol.Solution -> F.SimpC a -> ([F.KVar], Sol.Cand (F.KVar, Sol.EQual))
rhsCands s c    = (fst <$> ks, kqs)
  where
    kqs         = [ (p, (k, q)) | (k, su) <- ks, (p, q)  <- cnd k su ]
    ks          = predKs . F.crhs $ c
    cnd k su    = Sol.qbPreds msg s su (Sol.lookupQBind s k)
    msg         = "rhsCands: " ++ show (F.sid c)

predKs :: F.Expr -> [(F.KVar, F.Subst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k su) = [(k, su)]
predKs _              = []

--------------------------------------------------------------------------------
-- | Convert Solution into Result ----------------------------------------------
--------------------------------------------------------------------------------
result :: (F.Fixpoint a) => Config -> W.Worklist a -> Sol.Solution
       -> SolveM (F.Result (Integer, a))
--------------------------------------------------------------------------------
result cfg wkl !s = do
  lift $ writeLoud "Computing Result"
  stat    <- result_ wkl s -- >>= gradualSolve cfg
  lift $ whenNormal $ putStrLn $ "RESULT: " ++ show (F.sid <$> stat)
  F.Result (ci <$> stat) <$> solResult wkl cfg s
  where
    ci c = (F.subcId c, F.sinfo c)

solResult :: Fixpoint a => W.Worklist a -> Config -> Sol.Solution -> SolveM (M.HashMap F.KVar F.Expr)
solResult w cfg sol = (updateGradualSolution (W.unsatCandidates w) sol) >>= minimizeResult cfg . Sol.result

result_ ::Fixpoint a =>  W.Worklist a -> Sol.Solution -> SolveM (F.FixResult (F.SimpC a))
result_  w s = res <$> filterM (isUnsat s) cs
  where
    cs       = W.unsatCandidates w
    res []   = F.Safe
    res cs'  = F.Unsafe cs'


--------------------------------------------------------------------------------
-- | `minimizeResult` transforms each KVar's result to minimize it by removing
--   predicates that are implied by others. That is,
--
--      minimizeConjuncts :: ps:[Pred] -> {qs:[Pred] | subset qs ps}
--
--   such that `minimizeConjuncts ps` is a minimal subset of ps where no
--   is implied by /\_{q' in qs \ qs}
--
--------------------------------------------------------------------------------
minimizeResult :: Config -> M.HashMap F.KVar F.Expr
               -> SolveM (M.HashMap F.KVar F.Expr)
--------------------------------------------------------------------------------
minimizeResult cfg s
  | minimalSol cfg = mapM minimizeConjuncts s
  | otherwise      = return s

minimizeConjuncts :: F.Expr -> SolveM F.Expr
minimizeConjuncts p = F.pAnd <$> go (F.conjuncts p) []
  where
    go []     acc   = return acc
    go (p:ps) acc   = do b <- isValid (F.pAnd (acc ++ ps)) p
                         if b then go ps acc
                              else go ps (p:acc)


--------------------------------------------------------------------------------
updateGradualSolution :: Fixpoint a => [F.SimpC a] -> Sol.Solution -> SolveM (Sol.Solution)
--------------------------------------------------------------------------------
updateGradualSolution cs sol = foldM f (Sol.emptyGMap sol) cs 
  where
   f s c = do
    be <- getBinds
    let lpi = S.lhsPredGradual be sol c 
    let rp  = rhsPred c 
    gbs    <- firstValid rp lpi 
    return $ traceShow ("UPDATE SOLUTION FOR " ++ show (F._cid c) ++ "\n LEN GBS" ++ show (length gbs) ++ "\n\n" ++ show lpi ++ "\n\n" ++ showpp gbs  ++ "\nCONSTRAIN: \n" ++ show c) $ Sol.updateGMapWithKey gbs s 


firstValid :: Monoid a =>  F.Expr -> [(a, F.Expr)] -> SolveM a 
firstValid _   [] = return mempty 
firstValid rhs ((y,lhs):xs) = do
  v <- isValid lhs rhs
  if v then return y else firstValid rhs xs 


--------------------------------------------------------------------------------
isUnsat :: Fixpoint a => Sol.Solution -> F.SimpC a -> SolveM Bool
--------------------------------------------------------------------------------
isUnsat s c = do
  -- lift   $ printf "isUnsat %s" (show (F.subcId c))
  _     <- tickIter True -- newScc
  be    <- getBinds
  let lpi = S.lhsPredGradual be s c
  let rp = rhsPred        c
  res   <- (not . or) <$> mapM (`isValid` rp) (snd <$> lpi)
  lift   $ whenLoud $ showUnsat res (F.subcId c) (F.pOr (snd <$> lpi)) rp
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
isValid !p !q = (not . null) <$> filterValid [p] [(q, ())]


--------------------------------------------------------------------------------
-- | Solve with Gradual Types: 
-- | replace the unsat VC
-- | x1:r1, ... xi:??, ..., xn:rn |- p => q
-- | with 
-- | x1:r1, ... xi:forall x1..xi-1. (r1 ... /\ ri-1 => q), ... xn:rn |- p => q
--------------------------------------------------------------------------------

gradualSolve :: (Fixpoint a)
             => Config
             -> F.FixResult (F.SimpC a)
             -> SolveM (F.FixResult (F.SimpC a))
gradualSolve _  r = return r
{-
gradualSolve cfg (F.Unsafe cs)
  | gradual cfg   = go cs
  where
    go cs         = smtEnablembqi >> (makeResult . catMaybes <$> mapM gradualSolveOne cs)
    makeResult    = applyNonNull F.Safe F.Unsafe

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

makeGradualExpression :: [(F.Symbol, F.SortedReft)] -> [(F.Symbol, F.SortedReft)] -> F.Expr -> F.Expr
makeGradualExpression γ γ' p
  = F.PAll bs (F.PImp gs p)
  where
    bs = [ (x, s) | (x, F.RR s _) <- γ']
    gs = F.pAnd (bindToLogic <$> (γ ++ γ'))
    bindToLogic (x, F.RR _ (F.Reft (v, e))) = e `F.subst1` (v, F.EVar x)


-- makeEnvironment :: F.TaggedC c a => c a -> SolveM [(F.Symbol, F.SortedReft)]
makeEnvironment :: F.SimpC a -> SolveM [(F.Symbol, F.SortedReft)]
makeEnvironment c = cstrBinders c . F.soeBinds <$> getBinds

cstrBinders :: F.SimpC a -> F.BindEnv -> [(F.Symbol, F.SortedReft)]
cstrBinders c be = [ F.lookupBindEnv i be | i <- is  ]
  where
    is           = sort $ F.elemsIBindEnv $ F.senv c

splitLastGradual :: [(a, F.SortedReft)] -> ([(a, F.SortedReft)], [(a, F.SortedReft)], Bool)
splitLastGradual = go [] . reverse
  where
    go acc (xe@(x, F.RR s (F.Reft (v, e))) : xss)
      | Just es <- removePGrads e
      = (reverse ((x, F.RR s (F.Reft (v, F.pAnd es))):xss), reverse acc, True)
      | otherwise
      = go (xe:acc) xss
    go acc []
      = ([], reverse acc, False)

removePGrads :: F.Expr -> Maybe [F.Expr]
removePGrads (F.PAnd es)
  | F.PGrad `elem` es
  = Just $ filter (/= F.PGrad) es
  | otherwise
  = Nothing
removePGrads F.PGrad
  = Just []
removePGrads _
  = Nothing
-}

{-
---------------------------------------------------------------------------
donePhase' :: String -> SolveM ()
---------------------------------------------------------------------------
donePhase' msg = lift $ do
  threadDelay 25000
  putBlankLn
  donePhase Loud msg
-}
