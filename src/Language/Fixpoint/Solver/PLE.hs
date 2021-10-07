--------------------------------------------------------------------------------
-- | This module implements "Proof by Logical Evaluation" where we 
--   unfold function definitions if they *must* be unfolded, to strengthen
--   the environments with function-definition-equalities. 
--   The algorithm is discussed at length in:
-- 
--     1. "Refinement Reflection", POPL 2018, https://arxiv.org/pdf/1711.03842
--     2. "Reasoning about Functions", VMCAI 2018, https://ranjitjhala.github.io/static/reasoning-about-functions.pdf 
--------------------------------------------------------------------------------

{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}

module Language.Fixpoint.Solver.PLE (instantiate) where

import           Language.Fixpoint.Types hiding (simplify)
import           Language.Fixpoint.Types.Config  as FC
import           Language.Fixpoint.Types.Solutions (CMap)
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc 
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import qualified Language.Fixpoint.Utils.Trie    as T 
import           Language.Fixpoint.Utils.Progress 
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Graph.Deps             (isTarget) 
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Language.Fixpoint.Solver.Rewrite

import Language.REST.AbstractOC as OC
import Language.REST.ExploredTerms as ET
import Language.REST.Path
import Language.REST.RuntimeTerm as RT
import Language.REST.Rest (rest, terms, termsResult)
import Language.REST.Dot
import Language.REST.RESTDot
import Language.REST.RewriteRule
import Language.REST.OrderingConstraints.Strict
import Language.REST.OrderingConstraints.Lazy
import Language.REST.OrderingConstraints.ADT (ConstraintsADT)
import Language.REST.Op
import Language.REST.SMT (withZ3, SolverHandle)

import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           GHC.Generics
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb
import qualified Data.Text            as Tx
import           Debug.Trace          (trace)
import Text.Printf

type OCType = ConstraintsADT

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp

traceE :: (Expr,Expr) -> (Expr,Expr)
traceE (e,e')
  | isEnabled
  , e /= e'
  = trace ("\n" ++ showpp e ++ " ~> " ++ showpp e') (e,e')
  | otherwise
  = (e,e')
  where
    isEnabled :: Bool
    isEnabled = False

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instantiate :: (Fixpoint a, Loc a) => Config -> SInfo a -> Maybe [SubcId] -> IO (SInfo a)
instantiate cfg fi' subcIds = do
<<<<<<< HEAD
    let cs = [ (i, c) | (i, c) <- M.toList (cm fi), isPleCstr aEnv i c,
               maybe True (i `L.elem`) subcIds ]
    let t  = mkCTrie cs                                                 -- 1. BUILD the Trie
    res   <- withZ3 $ \z3 -> withProgress (1 + length cs) $
               withCtx cfg file sEnv (pleTrie t . instEnv cfg fi cs z3) -- 2. TRAVERSE Trie to compute InstRes
    return $ resSInfo cfg sEnv fi res                                   -- 3. STRENGTHEN SInfo using InstRes
=======
    let cs = M.filterWithKey
               (\i c -> isPleCstr aEnv i c && maybe True (i `L.elem`) subcIds)
               (cm fi)
    let t  = mkCTrie (M.toList cs)                                    -- 1. BUILD the Trie
    res   <- withProgress (1 + M.size cs) $
               withCtx cfg file sEnv (pleTrie t . instEnv cfg fi cs)  -- 2. TRAVERSE Trie to compute InstRes
    return $ resSInfo cfg sEnv fi res                                 -- 3. STRENGTHEN SInfo using InstRes
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512
  where
    file   = srcFile cfg ++ ".evals"
    sEnv   = symbolEnv cfg fi
    aEnv   = ae fi 
    fi     = normalize fi' 



------------------------------------------------------------------------------- 
-- | Step 1a: @instEnv@ sets up the incremental-PLE environment 
<<<<<<< HEAD
instEnv :: (Loc a) => Config -> SInfo a -> [(SubcId, SimpC a)] -> SolverHandle -> SMT.Context -> InstEnv a
instEnv cfg fi cs z3 ctx = InstEnv cfg ctx bEnv aEnv cs γ s0
=======
instEnv :: (Loc a) => Config -> SInfo a -> CMap (SimpC a) -> SMT.Context -> InstEnv a
instEnv cfg fi cs ctx = InstEnv cfg ctx bEnv aEnv cs γ s0
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512
  where 
    bEnv              = bs fi
    aEnv              = ae fi
    γ                 = knowledge cfg ctx fi  
    s0                = EvalEnv (SMT.ctxSymEnv ctx) mempty (defFuelCount cfg) (ET.empty ef) z3
    ef                = EF (OC.union (ordConstraints z3)) (OC.notStrongerThan (ordConstraints z3))

---------------------------------------------------------------------------------------------- 
-- | Step 1b: @mkCTrie@ builds the @Trie@ of constraints indexed by their environments
--
-- The trie is a way to unfold the equalities a minimum number of times.
-- Say you have
--
-- > 1: [1, 2, 3, 4, 5] => p1
-- > 2: [1, 2, 3, 6, 7] => p2
--
-- Then you build the tree
--
-- >  1 -> 2 -> 3 -> 4 -> 5 — [Constraint 1]
-- >            | -> 6 -> 7 — [Constraint 2]
--
-- which you use to unfold everything in 1, 2, and 3 once (instead of twice)
-- and with the proper existing environment
--
mkCTrie :: [(SubcId, SimpC a)] -> CTrie 
mkCTrie ics  = T.fromList [ (cBinds c, i) | (i, c) <- ics ]
  where
    cBinds   = L.sort . elemsIBindEnv . senv 

---------------------------------------------------------------------------------------------- 
-- | Step 2: @pleTrie@ walks over the @CTrie@ to actually do the incremental-PLE
pleTrie :: Fixpoint a => CTrie -> InstEnv a -> IO InstRes
pleTrie t env = loopT env ctx0 diff0 Nothing res0 t 
  where 
    diff0        = []
    res0         = M.empty 
    ctx0         = initCtx env ((mkEq <$> es0) ++ (mkEq' <$> es0'))
    es0          = L.filter (null . eqArgs) (aenvEqs   . ieAenv $ env)
    es0'         = L.filter (null . smArgs) (aenvSimpl . ieAenv $ env)
    mkEq  eq     = (EVar $ eqName eq, eqBody eq)
    mkEq' rw     = (EApp (EVar $ smName rw) (EVar $ smDC rw), smBody rw)

<<<<<<< HEAD
loopT :: Fixpoint a => InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CTrie -> IO InstRes
=======
loopT
  :: InstEnv a
  -> ICtx
  -> Diff         -- ^ The longest path suffix without forks in reverse order
  -> Maybe BindId -- ^ bind id of the branch ancestor of the trie if any.
                  --   'Nothing' when this is the top-level trie.
  -> InstRes
  -> CTrie
  -> IO InstRes
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512
loopT env ctx delta i res t = case t of 
  T.Node []  -> return res
  T.Node [b] -> loopB env ctx delta i res b
  T.Node bs  -> withAssms env ctx delta Nothing $ \ctx' -> do 
                  (ctx'', res') <- ple1 env ctx' i res 
                  foldM (loopB env ctx'' [] i) res' bs

<<<<<<< HEAD
loopB :: Fixpoint a => InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CBranch -> IO InstRes
=======
loopB
  :: InstEnv a
  -> ICtx
  -> Diff         -- ^ The longest path suffix without forks in reverse order
  -> Maybe BindId -- ^ bind id of the branch ancestor of the branch if any.
                  --   'Nothing' when this is a branch of the top-level trie.
  -> InstRes
  -> CBranch
  -> IO InstRes
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512
loopB env ctx delta iMb res b = case b of 
  T.Bind i t -> loopT env ctx (i:delta) (Just i) res t
  T.Val cid  -> withAssms env ctx delta (Just cid) $ \ctx' -> do 
                  progressTick
                  (snd <$> ple1 env ctx' iMb res) 

<<<<<<< HEAD

withAssms :: Fixpoint a => InstEnv a -> ICtx -> Diff -> Maybe SubcId -> (ICtx -> IO b) -> IO b
=======
-- | Adds to @ctx@ candidate expressions to unfold from the bindings in @delta@
-- and the rhs of @cidMb@.
--
-- Adds to @ctx@ assumptions from @env@ and @delta@ plus rewrites that
-- candidates can use.
--
-- Sets the current constraint id in @ctx@ to @cidMb@.
--
-- Pushes assumptions from the modified context to the SMT solver, runs @act@,
-- and then pops the assumptions.
--
withAssms :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> (ICtx -> IO b) -> IO b 
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512
withAssms env@(InstEnv {..}) ctx delta cidMb act = do 
  let ctx'  = updCtx env ctx delta cidMb 
  let assms = icAssms ctx'
  SMT.smtBracket ieSMT  "PLE.evaluate" $ do
    forM_ assms (SMT.smtAssert ieSMT) 
    act ctx'

-- | @ple1@ performs the PLE at a single "node" in the Trie 
ple1 :: InstEnv a -> ICtx -> Maybe BindId -> InstRes -> IO (ICtx, InstRes)
ple1 (InstEnv {..}) ctx i res = 
  updCtxRes res i <$> evalCandsLoop ieCfg ctx ieSMT ieKnowl ieEvEnv


evalToSMT :: String -> Config -> SMT.Context -> (Expr, Expr) -> Pred 
evalToSMT msg cfg ctx (e1,e2) = toSMT ("evalToSMT:" ++ msg) cfg ctx [] (EEq e1 e2)

evalCandsLoop :: Config -> ICtx -> SMT.Context -> Knowledge -> EvalEnv -> IO ICtx 
evalCandsLoop cfg ictx0 ctx γ env = go ictx0 0
  where
    withRewrites exprs =
      let
        rws = [rewrite e rw | rw <- knSims γ
                            ,  e <- S.toList (snd `S.map` exprs)]
      in 
        exprs <> (S.fromList $ concat rws)
    go ictx _ | S.null (icCands ictx) = return ictx
    go ictx i =  do
                  -- printf "Loop %s\n" (show i)
                  let cands = icCands ictx
                  let env' = env { evAccum = icEquals ictx <> evAccum env 
                                 , evFuel  = icFuel   ictx 
                                 }
                  (ictx', evalResults)  <- SMT.smtBracket ctx "PLE.evaluate" $ do
                               SMT.smtAssert ctx (pAnd (S.toList $ icAssms ictx)) 
                               foldM (evalOneCandStep γ env' i) (ictx, []) (S.toList cands)
                               -- foldM (\ictx e -> undefined) 
                               -- mapM (evalOne γ env' ictx) (S.toList cands)
                  let us = mconcat evalResults 
                  if S.null (us `S.difference` icEquals ictx)
                        then return ictx 
                        else do  let oks      = fst `S.map` us
                                 let us'      = withRewrites us 
                                 let eqsSMT   = evalToSMT "evalCandsLoop" cfg ctx `S.map` us'
                                 let ictx''   = ictx' { icSolved = icSolved ictx <> oks 
                                                      , icEquals = icEquals ictx <> us'
                                                      , icAssms  = icAssms  ictx <> S.filter (not . isTautoPred) eqsSMT }
                                 let newcands = mconcat (makeCandidates γ ictx'' <$> S.toList (cands <> (snd `S.map` us)))
                                 go (ictx'' { icCands = S.fromList newcands}) (i + 1)
                                 
-- evalOneCands :: Knowledge -> EvalEnv -> ICtx -> [Expr] -> IO (ICtx, [EvAccum])
-- evalOneCands γ env' ictx = foldM step (ictx, [])
evalOneCandStep :: Knowledge -> EvalEnv -> Int -> (ICtx, [EvAccum]) -> Expr -> IO (ICtx, [EvAccum])
evalOneCandStep γ env' i (ictx, acc) e = do
  (res, fm) <- evalOne γ env' ictx i e
  return (ictx { icFuel = fm}, res : acc)

rewrite :: Expr -> Rewrite -> [(Expr,Expr)] 
rewrite e rw = Mb.catMaybes $ map (`rewriteTop` rw) (notGuardedApps e)

rewriteTop :: Expr -> Rewrite -> Maybe (Expr,Expr) 
rewriteTop e rw
  | (EVar f, es) <- splitEApp e
  , f == smDC rw
  , length es == length (smArgs rw)
  = Just (EApp (EVar $ smName rw) e, subst (mkSubst $ zip (smArgs rw) es) (smBody rw))
  | otherwise
  = Nothing

---------------------------------------------------------------------------------------------- 
-- | Step 3: @resSInfo@ uses incremental PLE result @InstRes@ to produce the strengthened SInfo 
---------------------------------------------------------------------------------------------- 

resSInfo :: Config -> SymEnv -> SInfo a -> InstRes -> SInfo a
resSInfo cfg env fi res = strengthenBinds fi res' 
  where
    res'     = M.fromList $ zip is ps''
    ps''     = zipWith (\i -> elaborate (atLoc dummySpan ("PLE1 " ++ show i)) env) is ps' 
    ps'      = defuncAny cfg env ps
    (is, ps) = unzip (M.toList res)

---------------------------------------------------------------------------------------------- 
-- | @InstEnv@ has the global information needed to do PLE
---------------------------------------------------------------------------------------------- 

data InstEnv a = InstEnv 
  { ieCfg   :: !Config
  , ieSMT   :: !SMT.Context
  , ieBEnv  :: !BindEnv
  , ieAenv  :: !AxiomEnv 
  , ieCstrs :: !(CMap (SimpC a))
  , ieKnowl :: !Knowledge
  , ieEvEnv :: !EvalEnv
  } 

---------------------------------------------------------------------------------------------- 
-- | @ICtx@ is the local information -- at each trie node -- obtained by incremental PLE
---------------------------------------------------------------------------------------------- 

data ICtx    = ICtx 
  { icAssms    :: S.HashSet Pred            -- ^ Equalities converted to SMT format
  , icCands    :: S.HashSet Expr            -- ^ "Candidates" for unfolding
  , icEquals   :: EvAccum                   -- ^ Accumulated equalities
  , icSolved   :: S.HashSet Expr            -- ^ Terms that we have already expanded
  , icSimpl    :: !ConstMap                 -- ^ Map of expressions to constants
  , icSubcId   :: Maybe SubcId              -- ^ Current subconstraint ID
  , icFuel     :: !FuelCount                -- ^ Current fuel-count
  , icANFs     :: S.HashSet Pred            -- Hopefully contain only ANF things
  } 

---------------------------------------------------------------------------------------------- 
-- | @InstRes@ is the final result of PLE; a map from @BindId@ to the equations "known" at that BindId
---------------------------------------------------------------------------------------------- 

type InstRes = M.HashMap BindId Expr

---------------------------------------------------------------------------------------------- 
-- | @Unfold is the result of running PLE at a single equality; 
--     (e, [(e1, e1')...]) is the source @e@ and the (possible empty) 
--   list of PLE-generated equalities (e1, e1') ... 
---------------------------------------------------------------------------------------------- 

type CTrie   = T.Trie   SubcId
type CBranch = T.Branch SubcId
type Diff    = [BindId]    -- ^ in "reverse" order

initCtx :: InstEnv a -> [(Expr,Expr)] -> ICtx
initCtx env es   = ICtx 
  { icAssms  = mempty 
  , icCands  = mempty 
  , icEquals = S.fromList es
  , icSolved = mempty
  , icSimpl  = mempty 
  , icSubcId = Nothing
  , icFuel   = evFuel (ieEvEnv env)
  , icANFs   = mempty
  }

equalitiesPred :: S.HashSet (Expr, Expr) -> [Expr]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- S.toList eqs, e1 /= e2 ] 

updCtxRes :: InstRes -> Maybe BindId -> ICtx -> (ICtx, InstRes) 
updCtxRes res iMb ctx = (ctx, res')
  where 
    res' = updRes res iMb (pAnd $ equalitiesPred $ icEquals ctx)


updRes :: InstRes -> Maybe BindId -> Expr -> InstRes
updRes res (Just i) e = M.insert i e res 
updRes res  Nothing _ = res 

---------------------------------------------------------------------------------------------- 
-- | @updCtx env ctx delta cidMb@ adds the assumptions and candidates from @delta@ and @cidMb@ 
--   to the context. 
---------------------------------------------------------------------------------------------- 

updCtx :: Fixpoint a => InstEnv a -> ICtx -> Diff -> Maybe SubcId -> ICtx
updCtx InstEnv {..} ctx delta cidMb 
              = ctx { icAssms  = S.fromList (filter (not . isTautoPred) ctxEqs)  
                    , icCands  = S.fromList cands           <> icCands  ctx
                    , icEquals = initEqs                    <> icEquals ctx
                    , icSimpl  = M.fromList (S.toList sims) <> icSimpl ctx <> econsts
<<<<<<< HEAD
                    , icSubcId = fst <$> L.find (\(_, b) -> (head delta) `memberIBindEnv` (_cenv b)) ieCstrs
                    , icANFs   = anfs <> icANFs ctx
=======
                    , icSubcId = cidMb
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512
                    }
  where         
    initEqs   = S.fromList $ concat [rewrite e rw | e  <- cands ++ (snd <$> S.toList (icEquals ctx))
                                                  , rw <- knSims ieKnowl]
    anfs      = S.fromList (toSMT "updCtx" ieCfg ieSMT [] <$> L.nub [ expr xr | xr <- bs ])
    cands     = concatMap (makeCandidates ieKnowl ctx) (rhs:es)
    sims      = S.filter (isSimplification (knDCs ieKnowl)) (initEqs <> icEquals ctx)
    econsts   = M.fromList $ findConstants ieKnowl es
    ctxEqs    = toSMT "updCtx" ieCfg ieSMT [] <$> L.nub (concat
                  [ equalitiesPred initEqs 
                  , equalitiesPred sims 
                  , equalitiesPred (icEquals ctx)
                  , bexprs
                  ])
    bexprs    = [ expr xr   | xr@(_, r) <- bs, null (Vis.kvars r) ]
    bs        = unElab <$> binds
    (rhs:es)  = unElab <$> (eRhs : (expr <$> binds))
    eRhs      = maybe PTrue crhs subMb
<<<<<<< HEAD
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ]
    subMb     = getCstr (M.fromList ieCstrs) <$> cidMb
=======
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ] 
    subMb     = getCstr ieCstrs <$> cidMb
>>>>>>> 98e36e9b73062355a6864022395d8207e85c9512


findConstants :: Knowledge -> [Expr] -> [(Expr, Expr)]
findConstants γ es = [(EVar x, c) | (x,c) <- go [] (concatMap splitPAnd es)]  
  where 
    go su ess = if ess == ess' 
                  then su 
                  else go (su ++ su') ess' 
       where ess' = subst (mkSubst su') <$> ess
             su'  = makeSu ess 
    makeSu exprs  = [(x,c) | (EEq (EVar x) c) <- exprs 
                           , isConstant (knDCs γ) c
                           , EVar x /= c ]

makeCandidates :: Knowledge -> ICtx -> Expr -> [Expr]
makeCandidates γ ctx expr 
  = mytracepp ("\n" ++ show (length cands) ++ " New Candidates") cands
  where 
    cands = filter (\e -> isRedex γ e && not (e `S.member` icSolved ctx)) (notGuardedApps expr)

isRedex :: Knowledge -> Expr -> Bool 
isRedex γ e = isGoodApp γ e || isIte e 
  where 
    isIte EIte {} = True 
    isIte _       = False 


isGoodApp :: Knowledge -> Expr -> Bool 
isGoodApp γ e 
  | (EVar f, es) <- splitEApp e
  , Just i       <- L.lookup f (knSummary γ)
  = length es >= i
  | otherwise
  = False 
    



getCstr :: M.HashMap SubcId (SimpC a) -> SubcId -> SimpC a 
getCstr env cid = Misc.safeLookup "Instantiate.getCstr" cid env

isPleCstr :: AxiomEnv -> SubcId -> SimpC a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 

type EvAccum = S.HashSet (Expr, Expr)

--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evEnv      :: !SymEnv
  , evAccum    :: EvAccum
  , evFuel     :: FuelCount
  , explored   :: ExploredTerms RuntimeTerm (OCType Op) IO
  , z3         :: SolverHandle
  }

data FuelCount = FC 
  { fcMap :: M.HashMap Symbol Int
  , fcMax :: Maybe Int
  } 
  deriving (Show)

defFuelCount :: Config -> FuelCount
defFuelCount cfg = FC mempty (fuel cfg)

type EvalST a = StateT EvalEnv IO a
--------------------------------------------------------------------------------


getAutoRws :: Knowledge -> ICtx -> [AutoRewrite]
getAutoRws γ ctx =
  Mb.fromMaybe [] $ do
    cid <- icSubcId ctx
    M.lookup cid $ knAutoRWs γ

evalOne :: Knowledge -> EvalEnv -> ICtx -> Int -> Expr -> IO (EvAccum, FuelCount)
evalOne γ env ctx i e | i > 0 || null (getAutoRws γ ctx) = do
    ((e', _), st) <- runStateT (eval γ ctx NoRW e) (env { evFuel = icFuel ctx })
    let evAcc' = if (mytracepp ("evalOne: " ++ showpp e) e') == e then evAccum st else S.insert (e, e') (evAccum st)
    return (evAcc', evFuel st) 
evalOne γ env ctx _ e = do
  env' <- execStateT (evalREST γ ctx rp) (env { evFuel = icFuel ctx })
  return (evAccum env', evFuel env')
  where
    oc = ordConstraints (z3 env)
    rp = RP oc (map (,PLE) (pathTo [e])) constraints
    constraints = foldl go (OC.top oc) (pairs (pathTo [e]))
      where
        go c (t, u) = refine oc c t u

    pairs [] = []
    pairs xs = zip xs (tail xs)

    pathTo ts = ts

    -- Hack to get original path from subsequent PLE iterations
    -- pathTo ts | Just (t, _) <- L.find (\(t, t') -> t' == head ts && not (t `elem` ts)) $ S.toList (evAccum env)
    --           = pathTo (t:ts)
    -- pathTo ts | otherwise = ts

    -- pathTo e = L.last (L.sortOn length (pathsTo [e]))
    -- pathsTo ts =
    --   let
    --     heads = L.map fst $ L.filter (\(t, t') -> t' == head ts && not (t `elem` ts)) $ S.toList (evAccum env)
    --   in
    --     if heads == []
    --     then trace ("NO head for " ++ (show $ head ts)) [ts]
    --     else concatMap pathsTo (map (\h -> h:ts) heads)

-- | @notGuardedApps e@ yields all the subexpressions that are
-- applications not under an if-then-else, lambda abstraction, type abstraction,
-- type application, or quantifier.
notGuardedApps :: Expr -> [Expr]
notGuardedApps = go 
  where 
    go e@(EApp e1 e2)  = [e] ++ go e1 ++ go e2
    go (PAnd es)       = concatMap go es
    go (POr es)        = concatMap go es
    go (PAtom _ e1 e2) = go e1  ++ go e2
    go (PIff e1 e2)    = go e1  ++ go e2
    go (PImp e1 e2)    = go e1  ++ go e2 
    go (EBin  _ e1 e2) = go e1  ++ go e2
    go (PNot e)        = go e
    go (ENeg e)        = go e
    go e@(EIte b _ _)  = go b ++ [e] -- ++ go e1 ++ go e2  
    go (ECoerc _ _ e)  = go e 
    go (ECst e _)      = go e 
    go (ESym _)        = []
    go (ECon _)        = []
    go (EVar _)        = []
    go (ELam _ _)      = []
    go (ETApp _ _)     = []
    go (ETAbs _ _)     = []
    go (PKVar _ _)     = []
    go (PAll _ _)      = []
    go (PExist _ _)    = []
    go (PGrad{})       = []



data EvalType =
    NoRW       -- Normal PLE
  | FuncNormal -- Expand to Function Defs, stop before branch expansion
  | RWNormal   -- Fully Expand Defs in context of rewriting
  deriving (Eq)

newtype FinalExpand = FE Bool deriving (Show)

noExpand = FE False
expand = FE True

isExpand (FE f) = f

withFE :: (Expr -> Expr) -> (Expr, FinalExpand) -> (Expr, FinalExpand)
withFE f (e, fe) = (f e, fe)

feVal (FE f) = f

feAny xs = FE $ any id (map feVal xs)

feChoose (FE True) _ = expand
feChoose _                  f = f


feSeq :: [(Expr, FinalExpand)] -> ([Expr], FinalExpand)
feSeq xs = (map fst xs, feAny (map snd xs))

-- | Unfolds expressions using rewrites and equations.
--
-- Also reduces if-then-else when the boolean condition or the negation can be
-- proved valid. This is the actual implementation of guard-validation-before-unfolding
-- that is described in publications.
--
-- Also folds constants.
--
-- Also adds to the monad state all the subexpressions that have been rewritten
-- as pairs @(original_subexpression, rewritten_subexpression)@.
--
eval :: Knowledge -> ICtx -> EvalType -> Expr -> EvalST (Expr, FinalExpand)
eval _ ctx _ e
  | Just v <- M.lookup e (icSimpl ctx)
  = return (v, noExpand)
  
eval γ ctx et e =
  do acc <- gets (S.toList . evAccum)
     case L.lookup e acc of
        -- Just e' | et == NoRW -> eval γ ctx et e'
        _ -> do
          (e0', fe)  <- go e
          let e' = simplify γ ctx e0'
          if e /= e' 
            then
              case et of
                NoRW -> do
                  modify (\st -> st { evAccum = S.insert (traceE (e, e')) (evAccum st) })
                  (e'',  fe') <- eval γ (addConst (e,e') ctx) et e'
                  return (e'', feChoose fe fe')
                _ -> return (e', fe)
            else 
              return (e, fe)
  where
    addConst (e,e') ctx = if isConstant (knDCs γ) e'
                           then ctx { icSimpl = M.insert e e' $ icSimpl ctx} else ctx 
    go (ELam (x,s) e)   = withFE (ELam (x, s)) <$> eval γ' ctx et e where γ' = γ { knLams = (x, s) : knLams γ }
    go e@(EIte b e1 e2) = evalIte γ ctx et e b e1 e2
    go (ECoerc s t e)   = withFE (ECoerc s t)  <$> go e
    go e@(EApp _ _)     =
      case splitEApp e of
       (f, es) | et == RWNormal ->
          do
            (es', fe) <- feSeq <$> mapM (eval γ ctx et) es
            r <- if es /= es'
              then return (eApps f es', fe)
              else do
                (f', fe)  <- eval γ ctx et f
                (e', fe') <- evalApp γ ctx (eApps f' es) (f',es) et
                return $ (e', feChoose fe fe')
            -- liftIO $ printf "Simplify %s to %s\n" (show e) (show r)
            return r
       (f, es) ->
          do
            ((f':es'), fe) <- feSeq <$> mapM (eval γ ctx et) (f:es)
            (e', fe') <- evalApp γ ctx (eApps f' es) (f',es') et
            -- liftIO $ printf "Simplify %s to %s\n" (show e) (show e')
            return $ (e', feChoose fe fe')

    go e@(PAtom r e1 e2) = do
      b <- evalBool γ e
      case b of
        Just e' -> return (e', noExpand)
        _ -> do
          (e1', fe) <- go e1
          (e2', fe2) <- go e2
          return (PAtom r e1' e2', feChoose fe fe2)
    go (ENeg e)         = do (e', fe)  <- eval γ ctx et e
                             return $ ((ENeg e'), fe)
    go (EBin o e1 e2)   = do (e1', fe1) <- eval γ ctx et e1
                             (e2', fe2) <- eval γ ctx et e2
                             return (EBin o e1' e2', feChoose fe1 fe2)
    go (ETApp e t)      = withFE (flip ETApp t) <$> go e
    go (ETAbs e s)      = withFE (flip ETAbs s) <$> go e
    go e@(PNot e')      = fromMaybeM (withFE PNot <$> go e') (eb γ e)
    go e@(PImp e1 e2)   = fromMaybeM (both go PImp e1 e2) (eb γ e)
    go e@(PIff e1 e2)   = fromMaybeM (both go PIff e1 e2) (eb γ e)
    go e@(PAnd es)      = fromMaybeM (efAll PAnd (go  <$$> es))   (eb γ e)
    go e@(POr es)       = fromMaybeM (efAll POr (go <$$> es))    (eb γ e)
    go e                = return (e, noExpand)

    both f f' e1 e2 = do
      (e1', fe1) <- f e1
      (e2', fe2) <- f e2
      return (f' e1' e2', feChoose fe1 fe2)

    efAll f mes = do
      xs <- mes
      let (xs', fe) = feSeq xs
      return $ (f xs', fe)

    eb γ e = do
      b <- evalBool γ e
      return $ case b of
        Just x  -> Just (x, noExpand)
        Nothing -> Nothing

data RESTParams oc = RP
  { oc   :: AbstractOC oc Expr IO
  , path :: [(Expr, TermOrigin)]
  , c    :: oc
  }

getANFSubs :: Expr -> [(Symbol, Expr)]
getANFSubs (PAnd es)                                   = concatMap getANFSubs es
getANFSubs (EEq lhs rhs) | (EVar v) <- unElab lhs
                           , anfPrefix `isPrefixOfSym` v = [(v, unElab rhs)]
getANFSubs (EEq lhs rhs) | (EVar v) <- unElab rhs
                           , anfPrefix `isPrefixOfSym` v = [(v, unElab lhs)]
getANFSubs _                                           = []

-- Reverse the ANF transformation
deANF :: ICtx -> Expr -> Expr
deANF ctx e = subst' e where
  ints  = concatMap getANFSubs (S.toList $ icANFs ctx)
  ints' = map go (L.groupBy (\x y -> fst x == fst y) $ L.sortOn fst $ L.nub ints) where
    go ([(t, u)]) = (t, u)
    go ts         = (fst (head ts), getBest (map snd ts))
  su          = Su (M.fromList ints')
  subst' ee =
    let
      ee' = subst su ee
    in
      if ee == ee'
        then ee
        else subst' ee'

  getBest ts | Just t <- L.find isVar ts = t
    where
      -- Hack : Vars starting with ds_ are probably constants
      isVar (EVar t) = not $ Tx.isPrefixOf "ds_" (symbolText t)
      isVar _        = False

  -- If the only match is a ds_ var, use it
  getBest ts | Just t <- L.find isVar ts = t
    where
      isVar (EVar _) = True
      isVar _        = False

  getBest ts | otherwise = head ts

-- |
-- Adds to the monad state all the subexpressions that have been rewritten
-- as pairs @(original_subexpression, rewritten_subexpression)@.
--
-- Also folds constants.
--
-- The main difference with 'eval' is that 'evalREST' takes into account
-- autorewrites.
--
evalREST :: Knowledge -> ICtx -> RESTParams (OCType Op) -> EvalST ()
evalREST _ ctx rp
  | pathExprs <- map fst (mytracepp "EVAL1: path" $ path rp)
  , e         <- last pathExprs
  , Just v    <- M.lookup e (icSimpl ctx)
  = when (v /= e) $ modify (\st -> st { evAccum = S.insert (e, v) (evAccum st)})
        
evalREST γ ctx rp =
  do
    -- liftIO $ print $ length pathExprs
    exploredTerms <- gets explored
    -- when (ET.size exploredTerms > 25) $ error "boom"
    se <- liftIO (shouldExploreTerm exploredTerms e)
    when se $ do
      possibleRWs <- getRWs exploredTerms
      -- liftIO $ putStrLn "Check Start"
      rws <- notVisitedFirst exploredTerms <$> filterM (liftIO . allowed) possibleRWs
      (e', FE fe)   <- do
        r@(ec, _) <- eval γ ctx FuncNormal e
        if ec /= e
          then return r
          else eval γ ctx RWNormal e

      -- when (e' /= e) $
      -- liftIO $
      --   printf "%s \n i.e %s \n-> %s\n\n\n" (show $ convert e) (show $ convert (unsubst ctx e)) (show $ convert e') --

      let evalIsNewExpr = e' `L.notElem` pathExprs
      let exprsToAdd    = [e' | evalIsNewExpr]  ++ map fst rws
      let evAccum'      = S.fromList $ map (e,) $ exprsToAdd

      modify (\st ->
                st {
                  evAccum  = S.union evAccum' (evAccum st)
                , explored = ET.insert
                  (convert e)
                  (c rp)
                  (S.insert (convert e') $ S.fromList (map (convert . fst) possibleRWs))
                  (explored st)
                })

      when evalIsNewExpr $
        if fe && any isRW (path rp)
          then do
            r@(e'', _) <- eval γ (addConst (e, e')) NoRW e'
            return ()
            -- liftIO $
            --   printf "FINAL %s \n-> %s\n\n\n" (show $ convert e') (show $ convert e'') --
          else evalREST γ (addConst (e, e')) (rpEval e')

      mapM_ (\rw -> evalREST γ ctx (rpRW rw)) rws
  where
    shouldExploreTerm et e =
      case rwTerminationOpts rwArgs of
        RWTerminationCheckDisabled  -> return $ not $ visited (convert e) et
        RWTerminationCheckEnabled _ -> shouldExplore (convert e) (c rp) et

    allowed (rwE, c) | rwE `elem` pathExprs = return False
    allowed (_, c) | otherwise = termCheck c
    termCheck c = do
      -- putStrLn "Checking Termination"
      r <- passesTerminationCheck (oc rp) rwArgs c
      -- printf "Result: %s\n" (show r)
      return r

    notVisitedFirst et rws =
      let
        (v, nv) = L.partition (\(e, _) -> visited (convert e) et) rws
      in
        nv ++ v

    rpEval e' =
      let
        c' =
          if any isRW (path rp)
            then refine (oc rp) (c rp) e e'
            else c rp

      in
        rp{path = path rp ++ [(e', PLE)], c = c'}

    isRW (_, r) = r == RW

    rpRW (e', c') = rp{path = path rp ++ [(e', RW)], c = c' }

    pathExprs       = map fst (mytracepp "EVAL2: path" $ path rp)
    e               = last pathExprs
    autorws         = getAutoRws γ ctx

    rwArgs = RWArgs (isValid γ) $ knRWTerminationOpts γ

    -- getRWs et | debruijnIndex (unsubst ctx e) > 50 = return []
    getRWs et | otherwise =
      do
        ok <- if (isRW $ last (path rp)) then (return True) else (liftIO $ termCheck (c rp))
        if ok
          then
            do
              let e'         = deANF ctx e
              let getRW e ar = getRewrite (oc rp) rwArgs (c rp) e ar (shouldExploreTerm et)
              let getRWs' s  = Mb.catMaybes <$> mapM (liftIO . runMaybeT . getRW s) autorws
              -- liftIO $ printf "Considering %s subExprs\n" $ show (length (subExprs e'))
              concat <$> mapM getRWs' (subExprs e')
          else return []

    addConst (e,e') = if isConstant (knDCs γ) e'
                      then ctx { icSimpl = M.insert e e' $ icSimpl ctx} else ctx 

evalStep :: Knowledge -> ICtx -> Expr -> EvalST Expr
evalStep γ ctx (ELam (x,s) e)   = ELam (x, s) <$> evalStep γ' ctx e where γ' = γ { knLams = (x, s) : knLams γ }
evalStep γ ctx e@(EIte b e1 e2) = evalIte γ ctx e b e1 e2
evalStep γ ctx (ECoerc s t e)   = ECoerc s t <$> evalStep γ ctx e
evalStep γ ctx e@(EApp _ _)     = case splitEApp e of 
  (f, es) ->
    do
      f' <- evalStep γ ctx f
      if f' /= f
        then return (eApps f' es)
        else
          do
            es' <- mapM (evalStep γ ctx) es
            if es /= es'
              then return (eApps f' es')
              else evalApp γ ctx f' es'
evalStep γ ctx e@(PAtom r e1 e2) =
  fromMaybeM (PAtom r <$> evalStep γ ctx e1 <*> evalStep γ ctx e2) (evalBool γ e)
evalStep γ ctx (ENeg e) = ENeg <$> evalStep γ ctx e
evalStep γ ctx (EBin o e1 e2)   = do
  e1' <- evalStep γ ctx e1
  if e1' /= e1
    then return (EBin o e1' e2)
    else EBin o e1 <$> evalStep γ ctx e2
evalStep γ ctx (ETApp e t)      = flip ETApp t <$> evalStep γ ctx e
evalStep γ ctx (ETAbs e s)      = flip ETAbs s <$> evalStep γ ctx e
evalStep γ ctx e@(PNot e')      = fromMaybeM (PNot <$> evalStep γ ctx e') (evalBool γ e)
evalStep γ ctx e@(PImp e1 e2)   = fromMaybeM (PImp <$> evalStep γ ctx e1 <*> evalStep γ ctx e2) (evalBool γ e)
evalStep γ ctx e@(PIff e1 e2)   = fromMaybeM (PIff <$> evalStep γ ctx e1 <*> evalStep γ ctx e2) (evalBool γ e)
evalStep γ ctx e@(PAnd es)      = fromMaybeM (PAnd <$> (evalStep γ ctx <$$> es)) (evalBool γ e)
evalStep γ ctx e@(POr es)       = fromMaybeM (POr  <$> (evalStep γ ctx <$$> es)) (evalBool γ e)
evalStep _ _   e                = return e

fromMaybeM :: (Monad m) => m a -> m (Maybe a) -> m a 
fromMaybeM a ma = do 
  mx <- ma 
  case mx of 
    Just x  -> return x 
    Nothing -> a  

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs


-- | @evalApp kn ctx e es@ unfolds expressions in @eApps e es@ using rewrites
-- and equations
evalApp :: Knowledge -> ICtx -> (Expr, [Expr]) -> EvalType -> EvalST (Expr, FinalExpand)
evalApp γ ctx (EVar f, es) et
  | Just eq <- L.find ((== f) . eqName) (knAms γ) -- TODO:FUEL make this a fast lookup map!
  , length (eqArgs eq) <= length es 
  = do 
       env  <- gets (seSort . evEnv)
       okFuel <- checkFuel f
       if okFuel && et /= FuncNormal
         then do
                useFuel f
                let (es1,es2) = splitAt (length (eqArgs eq)) es
                shortcut noExpand (substEq env eq es1) es2 -- TODO:FUEL this is where an "unfolding" happens, CHECK/BUMP counter
         else return $ eApps (EVar f) es
  where
    shortcut et' (EIte i e1 e2) es2 = do
      (b, _) <- eval γ ctx et i
      b'  <- liftIO $ (mytracepp ("evalEIt POS " ++ showpp (i, b)) <$> isValid γ b)
      nb' <- liftIO $ (mytracepp ("evalEIt NEG " ++ showpp (i, PNot b)) <$> isValid γ (PNot b))
      r <- if b' 
        then shortcut noExpand e1 es2
        else if nb' then shortcut noExpand e2 es2
        else return $ (eApps (EIte b e1 e2) es2, expand)
      return r
    shortcut _ e' es2 = return $ (eApps e' es2, noExpand)

evalApp γ _ (EVar f) (e:es)
  | (EVar dc, as) <- splitEApp e
  , Just rw <- L.find (\rw -> smName rw == f && smDC rw == dc) (knSims γ)
  , length as == length (smArgs rw)
  = return (eApps (subst (mkSubst $ zip (smArgs rw) as) (smBody rw)) es, noExpand)

evalApp _ _ e es
  = return $ eApps e es

--------------------------------------------------------------------------------
-- | 'substEq' unfolds or instantiates an equation at a particular list of
--   argument values. We must also substitute the sort-variables that appear
--   as coercions. See tests/proof/ple1.fq
--------------------------------------------------------------------------------
substEq :: SEnv Sort -> Equation -> [Expr] -> Expr
substEq env eq es = subst su (substEqCoerce env eq es)
  where su = mkSubst $ zip (eqArgNames eq) es

substEqCoerce :: SEnv Sort -> Equation -> [Expr] -> Expr
substEqCoerce env eq es = Vis.applyCoSub coSub $ eqBody eq
  where 
    ts    = snd    <$> eqArgs eq
    sp    = panicSpan "mkCoSub"
    eTs   = sortExpr sp env <$> es
    coSub = mkCoSub env eTs ts

mkCoSub :: SEnv Sort -> [Sort] -> [Sort] -> Vis.CoSub
mkCoSub env eTs xTs = M.fromList [ (x, unite ys) | (x, ys) <- Misc.groupList xys ] 
  where
    unite ts    = Mb.fromMaybe (uError ts) (unifyTo1 senv ts)
    senv        = mkSearchEnv env
    uError ts   = panic ("mkCoSub: cannot build CoSub for " ++ showpp xys ++ " cannot unify " ++ showpp ts) 
    xys         = Misc.sortNub $ concat $ zipWith matchSorts _xTs _eTs
    (_xTs,_eTs) = (xTs, eTs)

matchSorts :: Sort -> Sort -> [(Symbol, Sort)]
matchSorts s1 s2 = go s1 s2
  where
    go (FObj x)      {-FObj-} y    = [(x, y)]
    go (FAbs _ t1)   (FAbs _ t2)   = go t1 t2
    go (FFunc s1 t1) (FFunc s2 t2) = go s1 s2 ++ go t1 t2
    go (FApp s1 t1)  (FApp s2 t2)  = go s1 s2 ++ go t1 t2
    go _             _             = []

--------------------------------------------------------------------------------

eqArgNames :: Equation -> [Symbol]
eqArgNames = map fst . eqArgs

evalBool :: Knowledge -> Expr -> EvalST (Maybe Expr) 
evalBool γ e = do 
  bt <- liftIO $ isValid γ e
  if bt then return $ Just PTrue 
   else do 
    bf <- liftIO $ isValid γ (PNot e)
    if bf then return $ Just PFalse 
          else return Nothing
               
evalIte :: Knowledge -> ICtx -> EvalType -> Expr -> Expr -> Expr -> EvalST (Expr, FinalExpand)
evalIte γ ctx b0 e1 e2 = do
  (b, fe) <- eval γ ctx b0
  b'  <- liftIO $ (mytracepp ("evalEIt POS " ++ showpp b) <$> isValid γ b)
  nb' <- liftIO $ (mytracepp ("evalEIt NEG " ++ showpp (PNot b)) <$> isValid γ (PNot b))
  if b' 
    then return (e1, noExpand)
    else if nb' then return $ (e2, noExpand)
    else return $ (EIte b e1 e2, fe)

--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge = KN 
  { knSims              :: ![Rewrite]           -- ^ Rewrite rules came from match and data type definitions 
  , knAms               :: ![Equation]          -- ^ All function definitions
  , knContext           :: SMT.Context
  , knPreds             :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
  , knLams              :: ![(Symbol, Sort)]
  , knSummary           :: ![(Symbol, Int)]     -- ^ summary of functions to be evaluates (knSims and knAsms) with their arity
  , knDCs               :: !(S.HashSet Symbol)  -- ^ data constructors drawn from Rewrite 
  , knSels              :: !SelectorMap 
  , knConsts            :: !ConstDCMap
  , knAutoRWs           :: M.HashMap SubcId [AutoRewrite]
  , knRWTerminationOpts :: RWTerminationOpts
  }

isValid :: Knowledge -> Expr -> IO Bool
isValid γ e = do 
  contra <- knPreds γ (knContext γ) (knLams γ) PFalse
  if contra 
    then return False 
    else knPreds γ (knContext γ) (knLams γ) e

knowledge :: Config -> SMT.Context -> SInfo a -> Knowledge
knowledge cfg ctx si = KN 
  { knSims                     = sims 
  , knAms                      = aenvEqs aenv
  , knContext                  = ctx 
  , knPreds                    = askSMT  cfg 
  , knLams                     = [] 
  , knSummary                  =    ((\s -> (smName s, 1)) <$> sims) 
                                 ++ ((\s -> (eqName s, length (eqArgs s))) <$> aenvEqs aenv)
                                 ++ lits
  , knDCs                      = S.fromList (smDC <$> sims) 
  , knSels                     = Mb.catMaybes $ map makeSel  sims 
  , knConsts                   = Mb.catMaybes $ map makeCons sims 
  , knAutoRWs                  = aenvAutoRW aenv
  , knRWTerminationOpts        =
      if (rwTerminationCheck cfg)
      then RWTerminationCheckEnabled (maxRWOrderingConstraints cfg)
      else RWTerminationCheckDisabled
  } 
  where 
    sims = aenvSimpl aenv ++ concatMap reWriteDDecl (ddecls si) 
    aenv = ae si

    lits = map toSum (toListSEnv (gLits si))
      where
        toSum (sym, sort)      = (sym, getArity sort)

        getArity (FFunc _ rhs) = 1 + getArity rhs
        getArity _             = 0



    makeCons rw 
      | null (syms $ smBody rw)
      = Just (smName rw, (smDC rw, smBody rw))
      | otherwise
      = Nothing 

    makeSel rw 
      | EVar x <- smBody rw
      = (smName rw,) . (smDC rw,) <$> L.elemIndex x (smArgs rw)
      | otherwise 
      = Nothing 

reWriteDDecl :: DataDecl -> [Rewrite]
reWriteDDecl ddecl = concatMap go (ddCtors ddecl) 
  where 
    go (DCtor f xs) = zipWith (\r i -> SMeasure r f' ys (EVar (ys!!i)) ) rs [0..]
       where 
        f'  = symbol f 
        rs  = (val . dfName) <$> xs  
        mkArg ws = zipWith (\_ i -> intSymbol (symbol ("darg"::String)) i) ws [0..]
        ys  = mkArg xs 

askSMT :: Config -> SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
askSMT cfg ctx bs e
--   | isContraPred e     = return False 
  | isTautoPred  e     = return True
  | null (Vis.kvars e) = SMT.checkValidWithContext ctx [] PTrue e'
  | otherwise          = return False
  where 
    e'                 = toSMT "askSMT" cfg ctx bs e 

toSMT :: String ->  Config -> SMT.Context -> [(Symbol, Sort)] -> Expr -> Pred
toSMT msg cfg ctx bs e = defuncAny cfg senv . elaborate "makeKnowledge" (elabEnv bs) . mytracepp ("toSMT from " ++ msg ++ showpp e)
                          $ e 
  where
    elabEnv      = insertsSymEnv senv
    senv         = SMT.ctxSymEnv ctx


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

withCtx :: Config -> FilePath -> SymEnv -> (SMT.Context -> IO a) -> IO a
withCtx cfg file env k = do
  ctx <- SMT.makeContextWithSEnv cfg file env
  _   <- SMT.smtPush ctx
  res <- k ctx
  _   <- SMT.cleanupContext ctx
  return res


-- (sel_i, D, i), meaning sel_i (D x1 .. xn) = xi, 
-- i.e., sel_i selects the ith value for the data constructor D  
type SelectorMap = [(Symbol, (Symbol, Int))]
type ConstDCMap = [(Symbol, (Symbol, Expr))]

-- ValueMap maps expressions to constants (including data constructors)
type ConstMap = M.HashMap Expr Expr
type LDataCon = Symbol              -- Data Constructors 

isSimplification :: S.HashSet LDataCon -> (Expr,Expr) -> Bool 
isSimplification dcs (_,c) = isConstant dcs c 
  

isConstant :: S.HashSet LDataCon -> Expr -> Bool 
isConstant dcs e = S.null (S.difference (exprSymbolsSet e) dcs)

class Simplifiable a where 
  simplify :: Knowledge -> ICtx -> a -> a 


instance Simplifiable Expr where
  simplify γ ictx e = mytracepp ("simplification of " ++ showpp e) $ fix (Vis.mapExpr tx) e 
    where 
      fix f e = if e == e' then e else fix f e' where e' = f e 
      tx e 
        | Just e' <- M.lookup e (icSimpl ictx)
        = e' 
      tx (EBin bop e1 e2) = applyConstantFolding bop e1 e2
      tx (ENeg e)         = applyConstantFolding Minus (ECon (I 0)) e
      tx (EApp (EVar f) a)
        | Just (dc, c)  <- L.lookup f (knConsts γ) 
        , (EVar dc', _) <- splitEApp a
        , dc == dc' 
        = c
      tx (EIte b e1 e2)
        | isTautoPred b  = e1 
        | isContraPred b = e2
      tx (ECoerc s t e)
        | s == t = e 
      tx (EApp (EVar f) a)
        | Just (dc, i)  <- L.lookup f (knSels γ) 
        , (EVar dc', es) <- splitEApp a
        , dc == dc' 
        = es!!i
      tx e = e
      
applyConstantFolding :: Bop -> Expr -> Expr -> Expr
applyConstantFolding bop e1 e2 =
  case (e1, e2) of
    ((ECon (R left)), (ECon (R right))) ->
      Mb.fromMaybe e (cfR bop left right)
    ((ECon (R left)), (ECon (I right))) ->
      Mb.fromMaybe e (cfR bop left (fromIntegral right))
    ((ECon (I left)), (ECon (R right))) ->
      Mb.fromMaybe e (cfR bop (fromIntegral left) right)
    ((ECon (I left)), (ECon (I right))) ->
      Mb.fromMaybe e (cfI bop left right)
    _ -> e
  where
    
    e = EBin bop e1 e2
    
    getOp :: Num a => Bop -> Maybe (a -> a -> a)
    getOp Minus    = Just (-)
    getOp Plus     = Just (+)
    getOp Times    = Just (*)
    getOp RTimes   = Just (*)
    getOp _        = Nothing

    cfR :: Bop -> Double -> Double -> Maybe Expr
    cfR bop left right = fmap go (getOp' bop)
      where
        go f = ECon $ R $ f left right
        
        getOp' Div      = Just (/)
        getOp' RDiv     = Just (/)
        getOp' op       = getOp op

    cfI :: Bop -> Integer -> Integer -> Maybe Expr
    cfI bop left right = fmap go (getOp' bop)
      where
        go f = ECon $ I $ f left right
        
        getOp' Mod = Just mod
        getOp' op  = getOp op


-------------------------------------------------------------------------------
-- | Normalization of Equation: make their arguments unique -------------------
-------------------------------------------------------------------------------

class Normalizable a where 
  normalize :: a -> a 

instance Normalizable (GInfo c a) where 
  normalize si = si {ae = normalize $ ae si}

instance Normalizable AxiomEnv where 
  normalize aenv = aenv { aenvEqs   = mytracepp "aenvEqs"  (normalize <$> aenvEqs   aenv)
                        , aenvSimpl = mytracepp "aenvSimpl" (normalize <$> aenvSimpl aenv) }

instance Normalizable Rewrite where 
  normalize rw = rw { smArgs = xs', smBody = normalizeBody (smName rw) $ subst su $ smBody rw }
    where 
      su  = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      xs  = smArgs rw 
      xs' = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (smName rw) i 


instance Normalizable Equation where 
  normalize eq = eq {eqArgs = zip xs' ss, eqBody = normalizeBody (eqName eq) $ subst su $ eqBody eq }
    where 
      su      = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      (xs,ss) = unzip (eqArgs eq) 
      xs'     = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (eqName eq) i 


normalizeBody :: Symbol -> Expr -> Expr
normalizeBody f = go   
  where 
    go e 
      | any (== f) (syms e) 
      = go' e 
    go e 
      = e 
    
    go' (PAnd [PImp c e1,PImp (PNot c') e2])
      | c == c' = EIte c e1 (go' e2)
    go' e = e 

_splitBranches :: Symbol -> Expr -> [(Expr, Expr)]
_splitBranches f = go   
  where 
    go (PAnd es) 
      | any (== f) (syms es) 
      = go' <$> es
    go e 
      = [(PTrue, e)]

    go' (PImp c e) = (c, e) 
    go' e          = (PTrue, e)

-- -- TODO:FUEL Config
-- maxFuel :: Int
-- maxFuel = 11 

useFuel :: Symbol -> EvalST ()
useFuel f = do 
  modify (\st -> st { evFuel = useFuelCount f (evFuel st) })

useFuelCount :: Symbol -> FuelCount -> FuelCount 
useFuelCount f fc = fc { fcMap = M.insert f (k + 1) m }
  where 
    k             = M.lookupDefault 0 f m 
    m             = fcMap fc

checkFuel :: Symbol -> EvalST Bool
checkFuel f = do 
  fc <- gets evFuel
  case (M.lookup f (fcMap fc), fcMax fc) of
    (Just fk, Just n) -> pure (fk <= n)
    _                 -> pure True
