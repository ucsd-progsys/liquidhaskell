{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

--------------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ---------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.GradualSolve (solveGradual) where

{- COMMENTING OUT AS IT DOESNT BUILD!
import           Control.Monad (when, filterM, foldM)
import           Control.Monad.State.Strict (lift)
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types.Solutions as Sol
import qualified Language.Fixpoint.SortCheck       as So
import           Language.Fixpoint.Types.PrettyPrint
import qualified Language.Fixpoint.Solver.GradualSolution  as S
import qualified Language.Fixpoint.Solver.Worklist  as W
import qualified Language.Fixpoint.Solver.Eliminate as E
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Graph
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
import           System.Console.CmdArgs.Verbosity (whenNormal, whenLoud)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
-}

import           Control.DeepSeq
import qualified Language.Fixpoint.Types           as F
import           Language.Fixpoint.Types.Config hiding (stats)

solveGradual :: (NFData a, F.Fixpoint a) => Config -> F.SInfo a -> IO (F.Result (Integer, a))
solveGradual = undefined



{- COMMENTING OUT AS IT DOESNT BUILD!

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
-- | tidyResult ensures we replace the temporary kVarArg names introduced to
--   ensure uniqueness with the original names in the given WF constraints.
--------------------------------------------------------------------------------
tidyResult :: F.Result a -> F.Result a
tidyResult r = r { F.resSolution  =  tidySolution  (F.resSolution r)
                 , F.gresSolution =  gtidySolution (F.gresSolution r)
                 }

tidySolution :: F.FixSolution -> F.FixSolution
tidySolution = fmap tidyPred

gtidySolution :: F.GFixSolution -> F.GFixSolution
gtidySolution = fmap tidyPred --  (\(e, es) -> (tidyPred e, tidyPred <$> es))

tidyPred :: F.Expr -> F.Expr
tidyPred = F.substf (F.eVar . F.tidySymbol)


predKs :: F.Expr -> [(F.KVar, F.Subst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k su) = [(k, su)]
predKs _              = []



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


-------------------------------------------------------------------------------
-- | solve with edits to allow Gradual types ----------------------------------
-------------------------------------------------------------------------------

solveGradual :: (NFData a, F.Fixpoint a) => Config -> F.SInfo a -> IO (F.Result (Integer, a))
-- solveGradual = undefined

solveGradual cfg fi = do
    (res, stat) <- withProgressFI sI $ runSolverM cfg sI n act
    when (solverStats cfg) $ printStats fi wkl stat
    return res
  where
    act  = solveGradual_ cfg fi s0 ks  wkl
    sI   = solverInfo cfg fi
    wkl  = W.init sI
    n    = fromIntegral $ W.wRanks wkl
    s0   = siSol  sI
    ks   = siVars sI

--------------------------------------------------------------------------------
solveGradual_ :: (NFData a, F.Fixpoint a)
       => Config
       -> F.SInfo a
       -> Sol.GSolution
       -> S.HashSet F.KVar
       -> W.Worklist a
       -> SolveM (F.Result (Integer, a), Stats)
--------------------------------------------------------------------------------
solveGradual_ cfg fi s0 ks wkl = do
  let s1  = mappend s0 $ {-# SCC "sol-init" #-} S.init cfg fi ks
  s2      <- {-# SCC "sol-local"  #-} filterLocal s1
  s       <- {-# SCC "sol-refine" #-} refine s2 wkl
  res     <- {-# SCC "sol-result" #-} result cfg wkl s
  st      <- stats
  let res' = {-# SCC "sol-tidy"   #-} tidyResult res
  return $!! (res', st)

filterLocal :: Sol.GSolution -> SolveM Sol.GSolution
filterLocal sol = do
  gs' <- mapM (initGBind sol) gs
  return $ Sol.updateGMap sol $ M.fromList gs'
  where
    gs = M.toList $ Sol.gMap sol

initGBind :: Sol.GSolution -> (F.KVar, (((F.Symbol, F.Sort), F.Expr), Sol.GBind)) -> SolveM (F.KVar, (((F.Symbol, F.Sort), F.Expr), Sol.GBind))
initGBind sol (k, (e, gb)) = do
   elems0  <- filterM (isLocal e) (Sol.gbEquals gb)
   elems   <- sortEquals elems0
   lattice <- makeLattice [] (map (:[]) elems) elems
   return $ ((k,) . (e,) . Sol.equalsGb) lattice
  where
    makeLattice acc new elems
      | null new
      = return acc
      | otherwise
      = do let cands = [e:es |e<-elems, es<-new]
           localCans <- filterM (isLocal e) cands
           newElems  <- filterM (notTrivial (new ++ acc)) localCans
           makeLattice (acc ++ new) newElems elems

    notTrivial [] _     = return True
    notTrivial (x:xs) p = do v <- isValid (mkPred x) (mkPred p)
                             if v then return False
                                  else notTrivial xs p

    mkPred eq = So.elaborate "initBGind.mkPred" (Sol.sEnv sol) (F.pAnd (Sol.eqPred <$> eq))
    isLocal (v, e) eqs = do
      let pp = So.elaborate "filterLocal" (Sol.sEnv sol) $ F.PExist [v] $ F.pAnd (e:(Sol.eqPred <$> eqs))
      isValid mempty pp

    root      = Sol.trueEqual
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
      ij <- isValid (mkPred [x]) (mkPred [y])
      return (if ij then [(j,i)] else [])

    mergeEdges es = filter (\(i,j) -> (not (any (\k -> ((i,k) `elem` es && (k,j) `elem` es)) (fst <$> es)))) es


--------------------------------------------------------------------------------
refine :: Sol.GSolution -> W.Worklist a -> SolveM Sol.GSolution
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
refineC :: Int -> Sol.GSolution -> F.SimpC a -> SolveM (Bool, Sol.GSolution)
---------------------------------------------------------------------------
refineC _i s c
  | null rhs  = return (False, s)
  | otherwise = do be      <- getBinds
                   let lhss = snd <$> S.lhsPred be s c
                   kqs     <- filterValidGradual lhss rhs
                   return   $ S.update s ks kqs
  where
    _ci       = F.subcId c
    (ks, rhs) = rhsCands s c
    -- msg       = printf "refineC: iter = %d, sid = %s, soln = \n%s\n"
    --               _i (show (F.sid c)) (showpp s)
    _msg ks xs ys = printf "refineC: iter = %d, sid = %s, s = %s, rhs = %d, rhs' = %d \n"
                     _i (show _ci) (showpp ks) (length xs) (length ys)


rhsCands :: Sol.GSolution -> F.SimpC a -> ([F.KVar], Sol.Cand (F.KVar, Sol.EQual))
rhsCands s c    = (fst <$> ks, kqs)
  where
    kqs         = [ (p, (k, q)) | (k, su) <- ks, (p, q)  <- cnd k su ]
    ks          = predKs . F.crhs $ c
    cnd k su    = Sol.qbPreds msg s su (Sol.lookupQBind s k)
    msg         = "rhsCands: " ++ show (F.sid c)

--------------------------------------------------------------------------------
-- | Gradual Convert Solution into Result ----------------------------------------------
--------------------------------------------------------------------------------
result :: (F.Fixpoint a) => Config -> W.Worklist a -> Sol.GSolution
       -> SolveM (F.Result (Integer, a))
--------------------------------------------------------------------------------
result cfg wkl s = do
  lift $ writeLoud "Computing Result"
  stat    <- result_ wkl s
  lift $ whenNormal $ putStrLn $ "RESULT: " ++ show (F.sid <$> stat)
  F.Result (ci <$> stat) <$> solResult cfg s <*> solResultGradual wkl cfg s
  where
    ci c = (F.subcId c, F.sinfo c)

result_ :: Fixpoint a =>  W.Worklist a -> Sol.GSolution -> SolveM (F.FixResult (F.SimpC a))
result_  w s = res <$> filterM (isUnsat s) cs
  where
    cs       = W.unsatCandidates w
    res []   = F.Safe
    res cs'  = F.Unsafe cs'

solResult :: Config -> Sol.GSolution -> SolveM (M.HashMap F.KVar F.Expr)
solResult cfg
  = minimizeResult cfg . Sol.result


solResultGradual :: W.Worklist a -> Config -> Sol.GSolution -> SolveM F.GFixSolution
solResultGradual w _cfg sol
  = F.toGFixSol . Sol.resultGradual <$> updateGradualSolution (W.unsatCandidates w) sol

--------------------------------------------------------------------------------
updateGradualSolution :: [F.SimpC a] -> Sol.GSolution -> SolveM (Sol.GSolution)
--------------------------------------------------------------------------------
updateGradualSolution cs sol = foldM f (Sol.emptyGMap sol) cs
  where
   f s c = do
    be <- getBinds
    let lpi = S.lhsPred be sol c
    let rp  = rhsPred c
    gbs    <- firstValid rp lpi
    return $ Sol.updateGMapWithKey gbs s


firstValid :: Monoid a =>  F.Expr -> [(a, F.Expr)] -> SolveM a
firstValid _   [] = return mempty
firstValid rhs ((y,lhs):xs) = do
  v <- isValid lhs rhs
  if v then return y else firstValid rhs xs


--------------------------------------------------------------------------------
isUnsat :: Fixpoint a => Sol.GSolution -> F.SimpC a -> SolveM Bool
--------------------------------------------------------------------------------
isUnsat s c = do
  -- lift   $ printf "isUnsat %s" (show (F.subcId c))
  _     <- tickIter True -- newScc
  be    <- getBinds
  let lpi = S.lhsPred be s c
  let rp = rhsPred        c
  res   <- (not . or) <$> mapM (`isValid` rp) (snd <$> lpi)
  lift   $ whenLoud $ showUnsat res (F.subcId c) (F.pOr (snd <$> lpi)) rp
  return res


-}
