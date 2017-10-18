{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

--------------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ---------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Solve (solve, solverInfo) where

import           Control.Monad (when, filterM)
import           Control.Monad.State.Strict (lift)
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Misc            as Misc
import qualified Language.Fixpoint.Types           as F
import qualified Language.Fixpoint.Types.Solutions as Sol
import qualified Language.Fixpoint.Types.Graduals  as G
import qualified Language.Fixpoint.Solver.GradualSolution as GS
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
import           System.Console.CmdArgs.Verbosity -- (whenNormal, whenLoud)
import           Control.DeepSeq
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List as L
import Control.Concurrent.ParallelIO.Global (parallel)

import qualified Language.Fixpoint.SortCheck       as So
import Language.Fixpoint.Solver.Sanitize (symbolEnv)
-- DEBUG
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
solve :: (NFData a, F.Fixpoint a, Show a, F.Loc a) => Config -> F.SInfo a -> IO (F.Result (Integer, a))
--------------------------------------------------------------------------------
solve cfg fi | gradual cfg
 = solveGradual cfg fi

solve cfg fi = do
    donePhase Misc.Loud "Worklist Initialize"
    (res, stat) <- withProgressFI sI $ runSolverM cfg sI act
    when (solverStats cfg) $ printStats fi wkl stat
    -- print (numIter stat)
    return res
  where
    act  = solve_ cfg fi s0 ks  wkl
    sI   = solverInfo cfg fi
    wkl  = W.init sI
    s0   = siSol  sI
    ks   = siVars sI


--------------------------------------------------------------------------------
solveGradual :: (NFData a, F.Fixpoint a, Show a, F.Loc a)
             => Config -> F.SInfo a -> IO (F.Result (Integer, a))
--------------------------------------------------------------------------------
solveGradual cfg fi = do
  -- graphStatistics cfg $ G.uniquify fi
  let fis = zip [1..] $ partition' Nothing $ G.uniquify fi
  if ginteractive cfg
    then snd . traceShow "FINAL SOLUTION\n"  <$> iSolveGradual cfg fis
    else snd . traceShow "FINAL SOLUTION\n" . mconcat <$> parallel (solveGradualOne cfg <$> fis)


iSolveGradual :: (NFData a, F.Fixpoint a, Show a, F.Loc a) => Config -> [(Int, F.SInfo a)] -> IO (Maybe G.GSol, F.Result (Integer, a))
iSolveGradual cfg fis
  = mconcat <$> parallel (solveGradualOne cfg <$> fis)


solveGradualOne :: (NFData a, F.Fixpoint a, Show a, F.Loc a) => Config -> (Int, F.SInfo a) -> IO (Maybe G.GSol, F.Result (Integer, a))
solveGradualOne cfg (_, fi) = do
  sols   <- makeSolutions cfg fi
  gradualLoop (cfg{gradual = False}) fi sols

gradualLoop :: (NFData a, F.Fixpoint a, Show a, F.Loc a) => Config -> F.SInfo a -> (Maybe [G.GSol]) -> IO (Maybe G.GSol, F.Result (Integer, a))
gradualLoop _ _ Nothing
  = return (Nothing, F.safe)
gradualLoop _ _ (Just [])
  = return (Nothing, F.unsafe)
gradualLoop cfg fi (Just (s:ss))
  = do whenLoud   $ putStrLn ("Solving for " ++ show s)
       whenNormal $ putStr "*"
       v <- getVerbosity
       -- putStr ("Substitution = " ++ show s)
       -- putStr ("BEFORE \n\n"  ++ (show $ F.toFixpoint cfg fi))
       -- putStr ("AFTER \n\n"  ++ (show $ F.toFixpoint cfg $ G.gsubst s fi))
       whenNormal $ setVerbosity Quiet
       r <- solve cfg (G.gsubst s fi)
       setVerbosity v
       whenLoud $ putStrLn ("Solution = " ++ if F.isUnsafe r then "UNSAFE" else "SAFE")
       if F.isUnsafe r
        then gradualLoop cfg fi (Just ss)
        else return (Just s, r)


makeSolutions :: (NFData a, F.Fixpoint a, Show a) => Config -> F.SInfo a -> IO (Maybe [G.GSol])
makeSolutions cfg fi
  = G.makeSolutions cfg fi <$> makeLocalLattice cfg fi (GS.init fi)



makeLocalLattice :: Config -> F.SInfo a
                 -> [(F.KVar, (F.GWInfo, [F.Expr]))]
                 -> IO [(F.KVar, (F.GWInfo, [[F.Expr]]))]
makeLocalLattice cfg fi kes = runSolverM cfg sI (act kes)
  where
    sI  = solverInfo cfg fi
    act = mapM (makeLocalLatticeOne cfg fi)


makeLocalLatticeOne :: Config -> F.SInfo a
            -> (F.KVar, (F.GWInfo, [F.Expr]))
            -> SolveM (F.KVar, (F.GWInfo, [[F.Expr]]))
makeLocalLatticeOne cfg fi (k, (e, es)) = do
   elems0  <- filterM (isLocal e) (map (:[]) es)
   elems   <- sortEquals elems0
   lattice <- makeLattice [] (map (:[]) elems) elems
   return $ ((k,) . (e,)) lattice
  where
    sEnv = symbolEnv cfg fi
    makeLattice acc new elems
      | null new
      = return {- traceShow ("LATTICE FROM ELEMENTS = " ++ showElems elems  ++ showElemss acc) -} acc
      | otherwise
      = do let cands = [e:es | e <- elems, es <- new]
           localCans <- filterM (isLocal e) cands
           newElems  <- filterM (notTrivial (new ++ acc)) localCans
           makeLattice (acc ++ new) newElems elems
    _showElem :: F.Expr -> String
    _showElem e1 = showpp $ F.subst (F.mkSubst [(x, F.EVar $ F.tidySymbol x) | x <- F.syms e1]) e1
    _showElems = unlines . map _showElem
    _showElemss = unlines. map _showElems

    notTrivial [] _     = return True
    notTrivial (x:xs) p = do v <- isValid F.dummySpan (mkPred x) (mkPred p)
                             if v then return False
                                  else notTrivial xs p

    mkPred es = So.elaborate "initBGind.mkPred" sEnv (F.pAnd es)

    isLocal i es = do
      let pp = So.elaborate "filterLocal" sEnv $ F.PExist [(F.gsym i, F.gsort i)] $ F.pAnd (F.gexpr i:es)
      isValid F.dummySpan mempty pp

    root      = mempty
    sortEquals xs = (bfs [0]) <$> makeEdges vs [] vs
      where
       vs        = zip [0..] (root:(head <$> xs))

       bfs []     _  = []
       bfs (i:is) es = (snd $ (vs!!i)) : bfs (is++map snd (filter (\(j,k) ->  (j==i && notElem k is)) es)) es

       makeEdges _   acc []    = return acc
       makeEdges vs acc (x:xs) = do ves  <- concat <$> mapM (makeEdgesOne x) vs
                                    if any (\(i,j) -> elem (j,i) acc) ves
                                      then makeEdges (filter ((/= fst x) . fst) vs) (filter (\(i,j) -> ((i /= fst x) && (j /= fst x))) acc) xs
                                      else makeEdges vs (mergeEdges (ves ++ acc)) xs

    makeEdgesOne (i,_) (j,_) | i == j = return []
    makeEdgesOne (i,x) (j,y) = do
      ij <- isValid F.dummySpan (mkPred [x]) (mkPred [y])
      return (if ij then [(j,i)] else [])

    mergeEdges es = filter (\(i,j) -> (not (any (\k -> ((i,k) `elem` es && (k,j) `elem` es)) (fst <$> es)))) es

--------------------------------------------------------------------------------

-- | Progress Bar
--------------------------------------------------------------------------------
withProgressFI :: SolverInfo a b -> IO b -> IO b
withProgressFI = withProgress . fromIntegral . cNumScc . siDeps
--------------------------------------------------------------------------------

printStats :: F.SInfo a ->  W.Worklist a -> Stats -> IO ()
printStats fi w s = putStrLn "\n" >> ppTs [ ptable fi, ptable s, ptable w ]
  where
    ppTs          = putStrLn . showpp . mconcat

--------------------------------------------------------------------------------
solverInfo :: Config -> F.SInfo a -> SolverInfo a b
--------------------------------------------------------------------------------
solverInfo cfg fI
  | useElim cfg = E.solverInfo cfg fI
  | otherwise   = SI mempty fI cD (siKvars fI)
  where
    cD          = elimDeps fI (kvEdges fI) mempty

siKvars :: F.SInfo a -> S.HashSet F.KVar
siKvars = S.fromList . M.keys . F.ws

--------------------------------------------------------------------------------
solve_ :: (NFData a, F.Fixpoint a, F.Loc a)
       => Config
       -> F.SInfo a
       -> Sol.Solution
       -> S.HashSet F.KVar
       -> W.Worklist a
       -> SolveM (F.Result (Integer, a), Stats)
--------------------------------------------------------------------------------
solve_ cfg fi s0 ks wkl = do
  let s1  = mappend s0 $ {-# SCC "sol-init" #-} S.init cfg fi ks
  s       <- {-# SCC "sol-refine" #-} refine s1 wkl
  res     <- {-# SCC "sol-result" #-} result cfg wkl s
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

--------------------------------------------------------------------------------
refine :: (F.Loc a) => Sol.Solution -> W.Worklist a -> SolveM Sol.Solution
--------------------------------------------------------------------------------
refine s w
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
refineC :: (F.Loc a) => Int -> Sol.Solution -> F.SimpC a
        -> SolveM (Bool, Sol.Solution)
---------------------------------------------------------------------------
refineC _i s c
  | null rhs  = return (False, s)
  | otherwise = do be     <- getBinds
                   let lhs = S.lhsPred be s c
                   kqs    <- filterValid (cstrSpan c) lhs rhs
                   return  $ S.update s ks kqs
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
result :: (F.Fixpoint a, F.Loc a) => Config -> W.Worklist a -> Sol.Solution
       -> SolveM (F.Result (Integer, a))
--------------------------------------------------------------------------------
result cfg wkl s = do
  lift $ writeLoud "Computing Result"
  stat    <- result_ wkl s
  lift $ whenLoud $ putStrLn $ "RESULT: " ++ show (F.sid <$> stat)
  F.Result (ci <$> stat) <$> solResult cfg s <*> return mempty
  where
    ci c = (F.subcId c, F.sinfo c)

solResult :: Config -> Sol.Solution -> SolveM (M.HashMap F.KVar F.Expr)
solResult cfg = minimizeResult cfg . Sol.result

result_ :: (F.Loc a) => W.Worklist a -> Sol.Solution -> SolveM (F.FixResult (F.SimpC a))
result_  w s = res <$> filterM (isUnsat s) cs
  where
    cs       = W.unsatCandidates w
    res []   = F.Safe
    res cs'  = F.Unsafe cs'

--------------------------------------------------------------------------------
-- | `minimizeResult` transforms each KVar's result by removing
--   conjuncts that are implied by others. That is,
--
--      minimizeConjuncts :: ps:[Pred] -> {qs:[Pred] | subset qs ps}
--
--   such that `minimizeConjuncts ps` is a minimal subset of ps where no
--   is implied by /\_{q' in qs \ qs}
--   see: tests/pos/min00.fq for an example.
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
    go (p:ps) acc   = do b <- isValid F.dummySpan (F.pAnd (acc ++ ps)) p
                         if b then go ps acc
                              else go ps (p:acc)

--------------------------------------------------------------------------------
isUnsat :: (F.Loc a) => Sol.Solution -> F.SimpC a -> SolveM Bool
--------------------------------------------------------------------------------
isUnsat s c = do
  -- lift   $ printf "isUnsat %s" (show (F.subcId c))
  _     <- tickIter True -- newScc
  be    <- getBinds
  let lp = S.lhsPred be s c
  let rp = rhsPred        c
  res   <- not <$> isValid (cstrSpan c) lp rp
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

--------------------------------------------------------------------------------
isValid :: F.SrcSpan -> F.Expr -> F.Expr -> SolveM Bool
--------------------------------------------------------------------------------
isValid sp p q = (not . null) <$> filterValid sp p [(q, ())]

cstrSpan :: (F.Loc a) => F.SimpC a -> F.SrcSpan
cstrSpan = F.srcSpan . F.sinfo

{-
---------------------------------------------------------------------------
donePhase' :: String -> SolveM ()
---------------------------------------------------------------------------
donePhase' msg = lift $ do
  threadDelay 25000
  putBlankLn
  donePhase Loud msg
-}


-- NV TODO Move to a new file
-------------------------------------------------------------------------------
-- | Interaction with the user when Solving -----------------------------------
-------------------------------------------------------------------------------

_iMergePartitions :: [(Int, F.SInfo a)] -> IO [(Int, F.SInfo a)]
_iMergePartitions ifis = do
  putStrLn "Current Partitions are: "
  putStrLn $ unlines (partitionInfo <$> ifis)
  putStrLn "Merge Partitions? Y/N"
  c <- getChar
  if c == 'N'
    then do putStrLn "Solving Partitions"
            return ifis
    else do
      (i, j) <- getMergePartition (length ifis)
      _iMergePartitions (mergePartitions i j ifis)

getMergePartition :: Int -> IO (Int, Int)
getMergePartition n = do
  putStrLn "Which two partition to merge? (i, j)"
  ic <- getLine
  let (i,j) = read ic :: (Int, Int)
  if i < 1 || n < i || j < 1 || n < j
    then do putStrLn ("Invalid Partition numbers, write (i,j) with 1 <= i <= " ++ show n)
            getMergePartition n
    else return (i,j)

mergePartitions :: Int -> Int -> [(Int, F.SInfo a)] -> [(Int, F.SInfo a)]
mergePartitions i j fis
  = zip [1..] ((takei i `mappend` (takei j){F.bs = mempty}):rest)
  where
    takei i = snd (fis L.!! (i - 1))
    rest = snd <$> filter (\(k,_) -> (k /= i && k /= j)) fis

partitionInfo :: (Int, F.SInfo a) -> String
partitionInfo (i, fi)
  = "Partition number " ++ show i ++ "\n" ++
    "Defined ?? " ++ show defs    ++ "\n" ++
    "Used ?? "    ++ show uses
  where
    gs   = F.wloc . snd <$> L.filter (F.isGWfc . snd) (M.toList (F.ws fi))
    defs = L.nub (F.gsrc <$> gs)
    uses = L.nub (F.gused <$> gs)
