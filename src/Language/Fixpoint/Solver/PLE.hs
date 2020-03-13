--------------------------------------------------------------------------------
-- | This module implements "Proof by Logical Evaluation" where we 
--   unfold function definitions if they *must* be unfolded, to strengthen
--   the environments with function-definition-equalities. 
--   The algorithm is discussed at length in:
-- 
--     1. "Refinement Reflection", POPL 2018, https://arxiv.org/pdf/1711.03842
--     2. "Reasoning about Functions", VMCAI 2018, https://ranjitjhala.github.io/static/reasoning-about-functions.pdf 
--------------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.Fixpoint.Solver.PLE (instantiate) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config  as FC
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc 
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import qualified Language.Fixpoint.Utils.Trie    as T 
import           Language.Fixpoint.Utils.Progress 
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Graph.Deps             (isTarget) 
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Control.Monad.State
import qualified Data.Text            as T
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb 
import           Data.Char            (isUpper)
-- import           Debug.Trace          (trace)

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp

traceE :: (Expr,Expr) -> (Expr,Expr)
traceE (e,e') 
  | True 
  , e /= e' 
  = tracepp ("\n" ++ showpp e ++ " ~> " ++ showpp e') (e,e') 
  | otherwise 
  = (e,e')

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instantiate :: (Loc a) => Config -> SInfo a -> IO (SInfo a)
instantiate cfg fi' = do 
    let cs = [ (i, c) | (i, c) <- M.toList (cm fi), isPleCstr aEnv i c ] 
    let t  = mkCTrie cs                                               -- 1. BUILD the Trie
    res   <- withProgress (1 + length cs) $ 
               withCtx cfg file sEnv (pleTrie t . instEnv cfg fi cs)  -- 2. TRAVERSE Trie to compute InstRes
    return $ resSInfo cfg sEnv fi res                                 -- 3. STRENGTHEN SInfo using InstRes
  where
    file   = srcFile cfg ++ ".evals"
    sEnv   = symbolEnv cfg fi
    aEnv   = ae fi 
    fi     = normalize fi' 



------------------------------------------------------------------------------- 
-- | Step 1a: @instEnv@ sets up the incremental-PLE environment 
instEnv :: (Loc a) => Config -> SInfo a -> [(SubcId, SimpC a)] -> SMT.Context -> InstEnv a 
instEnv cfg fi cs ctx = InstEnv cfg ctx bEnv aEnv (M.fromList cs) γ s0
  where 
    bEnv              = bs fi
    aEnv              = ae fi
    γ                 = knowledge cfg ctx fi  
    s0                = EvalEnv 0 [] aEnv (SMT.ctxSymEnv ctx) cfg 

---------------------------------------------------------------------------------------------- 
-- | Step 1b: @mkCTrie@ builds the @Trie@ of constraints indexed by their environments 
mkCTrie :: [(SubcId, SimpC a)] -> CTrie 
mkCTrie ics  = T.fromList [ (cBinds c, i) | (i, c) <- ics ]
  where
    cBinds   = L.sort . elemsIBindEnv . senv 

---------------------------------------------------------------------------------------------- 
-- | Step 2: @pleTrie@ walks over the @CTrie@ to actually do the incremental-PLE
pleTrie :: CTrie -> InstEnv a -> IO InstRes
pleTrie t env = loopT env ctx0 diff0 Nothing res0 t 
  where 
    diff0        = []
    res0         = M.empty 
    ctx0         = initCtx $ zip es0 (repeat PTrue)
    es0          = eqBody <$> L.filter (null . eqArgs) (aenvEqs . ieAenv $ env)

loopT :: InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CTrie -> IO InstRes
loopT env ctx delta i res t = case t of 
  T.Node []  -> return res
  T.Node [b] -> loopB env ctx delta i res b
  T.Node bs  -> withAssms env ctx delta Nothing $ \ctx' -> do 
                  (ctx'', res') <- ple1 env ctx' i res 
                  foldM (loopB env ctx'' [] i) res' bs

loopB :: InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CBranch -> IO InstRes
loopB env ctx delta iMb res b = case b of 
  T.Bind i t -> loopT env ctx (i:delta) (Just i) res t
  T.Val cid  -> withAssms env ctx delta (Just cid) $ \ctx' -> do 
                  progressTick
                  (snd <$> ple1 env ctx' iMb res) 


withAssms :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> (ICtx -> IO b) -> IO b 
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


evalToSMT :: Config -> SMT.Context -> (Expr, Expr) -> Pred 
evalToSMT cfg ctx (e1,e2) = toSMT cfg ctx [] (EEq e1 e2)

evalCandsLoop :: Config -> ICtx -> SMT.Context -> Knowledge -> EvalEnv -> IO ICtx 
evalCandsLoop cfg ictx0 ctx γ env = go ictx0 
  where 
    go ictx | S.null (icCands ictx) = return ictx 
    go ictx =  do let cands = S.toList (icCands ictx) 
                  eqs   <- SMT.smtBracket ctx "PLE.evaluate" $ do
                               SMT.smtAssert ctx (pAnd (icAssms ictx)) 
                               mapM (evalOne γ env) cands
                  case Mb.catMaybes eqs of 
                        [] -> return ictx 
                        us -> do let oks      = S.fromList (fst <$> us)
                                 let rws      = Mb.catMaybes [rewrite e rw | rw <- knSims γ, e <- (snd <$> us)]
                                 let us'      = us ++ rws 
                                 let eqsSMT   = evalToSMT cfg ctx <$> us
                                 let ictx'    = ictx { icSolved = icSolved ictx <> oks 
                                                     , icEquals = icEquals ictx <> us'
                                                     , icAssms  = icAssms  ictx <> eqsSMT }
                                 let newcands = concatMap (makeCandidates γ ictx') (cands ++ (snd <$> us))
                                 go (ictx' { icCands = S.fromList newcands})

rewrite :: Expr -> Rewrite -> Maybe (Expr,Expr) 
rewrite e rw
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
  , ieCstrs :: !(M.HashMap SubcId (SimpC a))
  , ieKnowl :: !Knowledge
  , ieEvEnv :: !EvalEnv
  } 

---------------------------------------------------------------------------------------------- 
-- | @ICtx@ is the local information -- at each trie node -- obtained by incremental PLE
---------------------------------------------------------------------------------------------- 

data ICtx    = ICtx 
  { icAssms  :: ![Pred]          -- ^ Equalities converted to SMT format 
  , icCands  :: S.HashSet Expr   -- ^ "Candidates" for unfolding
  , icEquals :: ![(Expr,Expr)]   -- ^ Accumulated equalities  
  , icSolved :: S.HashSet Expr   -- ^ Terms that we have already expanded
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

initCtx :: [(Expr,Expr)] -> ICtx
initCtx es = ICtx 
  { icAssms  = [] 
  , icCands  = mempty 
  , icEquals = es  
  , icSolved = mempty
  }

equalitiesPred :: [(Expr, Expr)] -> [Expr]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- eqs, e1 /= e2 ] 

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

updCtx :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> ICtx 
updCtx InstEnv {..} ctx delta cidMb 
              = ctx { icAssms  = ctxEqs  
                    , icCands  = S.fromList cands   <> icCands  ctx
                    , icEquals = initEqs <> icEquals ctx }
  where         
    initEqs   = initEqualities ieSMT ieAenv bs ++ 
                Mb.catMaybes [rewrite e rw | e <- cands, rw <- knSims ieKnowl] 
    cands     = concatMap (makeCandidates ieKnowl ctx) es
    ctxEqs    = toSMT ieCfg ieSMT [] <$> concat 
                  [ equalitiesPred initEqs 
                  , [ expr xr   | xr@(_, r) <- bs, null (Vis.kvars r) ] 
                  ]
    bs        = unElab <$> binds
    es        = unElab <$> (eRhs : (expr <$> binds))
    eRhs      = maybe PTrue crhs subMb
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ] 
    subMb     = getCstr ieCstrs <$> cidMb


makeCandidates :: Knowledge -> ICtx -> Expr -> [Expr]
makeCandidates γ ctx expr 
  = filter (\e -> isGoodApp e && (not (e `S.member` icSolved ctx))) (topApps expr)
  where 
    isGoodApp e 
      | (EVar f, es) <- splitEApp e
      , Just i       <- L.lookup f (knSummary γ)
      = length es == i
      | otherwise
      = False 


getCstr :: M.HashMap SubcId (SimpC a) -> SubcId -> SimpC a 
getCstr env cid = Misc.safeLookup "Instantiate.getCstr" cid env

isPleCstr :: AxiomEnv -> SubcId -> SimpC a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 


--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evId        :: !Int
  , evSequence  :: [(Expr,Expr)]
  , _evAEnv     :: !AxiomEnv
  , evEnv       :: !SymEnv
  , _evCfg      :: !Config
  }

type EvalST a = StateT EvalEnv IO a
--------------------------------------------------------------------------------

evalOne :: Knowledge -> EvalEnv -> Expr -> IO (Maybe (Expr, Expr))
evalOne γ env e = do
  e' <- evalStateT (eval γ initCS (mytracepp "evalOne: " e)) env 
  if e' == e then return Nothing else return (Just $ traceE (e,e'))

{- | [NOTE: Eval-Ite]  We should not be doing any PLE/eval under if-then-else where 
     the guard condition does not provably hold. For example, see issue #387.
     However, its ok and desirable to `eval` in this case, as long as one is not 
     unfolding recursive functions. To permit this, we track the "call-stack" and 
     whether or not, `eval` is occurring under an unresolved guard: if so, we do not 
     expand under any function that is already on the call-stack.
  -}

data Recur  = Ok | Stop deriving (Eq, Show)
type CStack = ([Symbol], Recur)

instance PPrint Recur where 
  pprintTidy _ = Misc.tshow 

initCS :: CStack 
initCS = ([], Ok)

pushCS :: CStack -> Symbol -> CStack 
pushCS (fs, r) f = (f:fs, r)

recurCS :: CStack -> Symbol -> Bool 
recurCS (_,  Ok) _ = True 
recurCS (fs, _) f  = not (f `elem` fs) 

noRecurCS :: CStack -> CStack 
noRecurCS (fs, _) = (fs, Stop)

-- Don't evaluate under Lam, App, Ite, or Constants
topApps :: Expr -> [Expr]
topApps = go 
  where 
    go (PAnd es)       = concatMap go es
    go (POr es)        = concatMap go es
    go (PAtom _ e1 e2) = go e1  ++ go e2
    go (PIff e1 e2)    = go e1  ++ go e2
    go (PImp e1 e2)    = go e1  ++ go e2
    go (EBin  _ e1 e2) = go e1  ++ go e2
    go (PNot e)        = go e
    go (ENeg e)        = go e
    go e@(EApp _ _)    = [e] -- go e1 ++ go e2 
    go _               = []

-- makeLam is the adjoint of splitEApp
makeLam :: Knowledge -> Expr -> Expr
makeLam γ e = L.foldl' (flip ELam) e (knLams γ)

eval :: Knowledge -> CStack -> Expr -> EvalST Expr
eval γ stk = go 
  where 
    go (ELam (x,s) e)   = ELam (x, s) <$> eval γ' stk e where γ' = γ { knLams = (x, s) : knLams γ }
    go e@(EIte b e1 e2) = go b        >>= \b' -> evalIte γ stk e b' e1 e2
    go (ECoerc s t e)   = ECoerc s t  <$> go e
    go e@(EApp _ _)     = evalArgs γ stk e >>= evalApp γ stk e 
    go e@(EVar _)       = evalApp  γ stk e (e, [])
    go (PAtom r e1 e2)  = PAtom r      <$> go e1 <*> go e2
    go (ENeg e)         = ENeg         <$> go e
    go (EBin o e1 e2)   = EBin o       <$> go e1 <*> go e2
    go (ETApp e t)      = flip ETApp t <$> go e
    go (ETAbs e s)      = flip ETAbs s <$> go e
    go (PNot e)         = PNot         <$> go e
    go (PImp e1 e2)     = PImp         <$> go e1 <*> go e2
    go (PIff e1 e2)     = PIff         <$> go e1 <*> go e2
    go (PAnd es)        = PAnd         <$> (go  <$$> es)
    go (POr es)         = POr          <$> (go  <$$> es)
    go e                = return e

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs

-- | `evalArgs` also evaluates all the partial applications for hacky reasons,
--   suppose `foo g = id` then we want `foo g 10 = 10` and for that we need 
--   to `eval` the term `foo g` into `id` to tickle the `eval` on `id 10`.
--   This seems a bit of a hack. At any rate, this can lead to divergence. 
--   TODO: distill a .fq test from the MOSSAKA-hw3 example.

evalArgs :: Knowledge -> CStack -> Expr -> EvalST (Expr, [Expr])
evalArgs γ stk e = go [] e 
  where
    go acc (EApp f e)
      = do f' <- evalOk γ stk f
           e' <- eval γ stk e
           go (e':acc) f'
    go acc e
      = (,acc) <$> eval γ stk e

-- | Minimal test case illustrating this `evalOk` hack is LH#tests/ple/pos/MossakaBug.hs
--   too tired & baffled to generate simple .fq version. TODO:nuke and rewrite PLE!
evalOk :: Knowledge -> CStack -> Expr -> EvalST Expr
evalOk γ stk@(_, Ok) e = eval γ stk e 
evalOk _ _           e = pure e 

{- 
evalArgs :: Knowledge -> CStack -> Expr -> EvalST (Expr, [Expr])
evalArgs 
  | True  = evalArgsOLD 
  | False = evalArgsNEW 

evalArgsNEW :: Knowledge -> CStack -> Expr -> EvalST (Expr, [Expr])
evalArgsNEW γ stk e = do 
    let (e1, es) = splitEApp e 
    e1' <- eval γ stk e1 
    es' <- mapM (eval γ stk) es 
    return (e1', es')

-}
    
evalApp :: Knowledge -> CStack -> Expr -> (Expr, [Expr]) -> EvalST Expr
-- evalApp γ stk e (e1, es) = tracepp ("evalApp:END" ++ showpp (e1,es)) <$> (evalAppAc γ stk e (e1, es))
evalApp γ stk e (e1, es) = do 
  res     <- evalAppAc γ stk e (e1, es)
  let diff = (res /= (eApps e1 es))
  return   $ mytracepp ("evalApp:END:" ++ showpp diff) res 

evalAppAc :: Knowledge -> CStack -> Expr -> (Expr, [Expr]) -> EvalST Expr

{- MOSSAKA-} 
evalAppAc γ stk e (EVar f, [ex])
  | (EVar dc, es) <- splitEApp ex
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (knSims γ)
  , length (smArgs simp) == length es
  = do let msg    = "evalAppAc:ePop: " ++ showpp (f, dc, es)
       let ePopIf = mytracepp msg $ substPopIf (zip (smArgs simp) es) (smBody simp)
       e'    <- eval γ stk ePopIf 
       (e, "Rewrite -" ++ showpp f) ~> e'

evalAppAc γ stk _ (EVar f, es)
  -- we should move the lookupKnowledge stuff here into kmAms γ
  | Just eq <- L.find (( == f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es
  , f `notElem` syms bd               -- non-recursive equations << HACK! misses MUTUALLY RECURSIVE definitions! 
  , recurCS stk f 
  = do env   <- seSort <$> gets evEnv
       let ee = substEq env PopIf eq es bd
       assertSelectors γ ee 
       eval γ (pushCS stk f) ee 

evalAppAc γ stk _e (EVar f, es)
  | Just eq <- L.find ((== f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es   -- recursive equations
  , recurCS stk f 
  = do env      <- seSort <$> gets evEnv
       mytracepp ("EVAL-REC-APP" ++ showpp (stk, _e)) 
         <$> evalRecApplication γ f (pushCS stk f) (eApps (EVar f) es) (substEq env Normal eq es bd)

evalAppAc _ _ _ (f, es)
  = return (eApps f es)

--------------------------------------------------------------------------------
-- | 'substEq' unfolds or instantiates an equation at a particular list of
--   argument values. We must also substitute the sort-variables that appear
--   as coercions. See tests/proof/ple1.fq
--------------------------------------------------------------------------------
substEq :: SEnv Sort -> SubstOp -> Equation -> [Expr] -> Expr -> Expr
substEq env o eq es bd = substEqVal o eq es (substEqCoerce env eq es bd)

data SubstOp = PopIf | Normal

substEqVal :: SubstOp -> Equation -> [Expr] -> Expr -> Expr
substEqVal o eq es bd = case o of
    PopIf  -> substPopIf     xes  bd
    Normal -> subst (mkSubst xes) bd
  where
    xes    =  zip xs es
    xs     =  eqArgNames eq

substEqCoerce :: SEnv Sort -> Equation -> [Expr] -> Expr -> Expr
substEqCoerce env eq es bd = Vis.applyCoSub coSub bd
  where 
    ts    = snd    <$> eqArgs eq
    sp    = panicSpan "mkCoSub"
    eTs   = sortExpr sp env <$> es
    coSub = mytracepp  ("substEqCoerce" ++ showpp (eqName eq, es, eTs, ts)) $ mkCoSub env eTs ts

mkCoSub :: SEnv Sort -> [Sort] -> [Sort] -> Vis.CoSub
mkCoSub env eTs xTs = M.fromList [ (x, unite ys) | (x, ys) <- Misc.groupList xys ] 
  where
    unite ts    = mytracepp ("UNITE: " ++ showpp ts) $ Mb.fromMaybe (uError ts) (unifyTo1 senv ts)
    senv        = mkSearchEnv env
    uError ts   = panic ("mkCoSub: cannot build CoSub for " ++ showpp xys ++ " cannot unify " ++ showpp ts) 
    xys         = mytracepp "mkCoSubXXX" $ Misc.sortNub $ concat $ zipWith matchSorts _xTs _eTs
    (_xTs,_eTs) = mytracepp "mkCoSub:MATCH" $ (xTs, eTs)

matchSorts :: Sort -> Sort -> [(Symbol, Sort)]
matchSorts s1 s2 = mytracepp  ("matchSorts :" ++ showpp (s1, s2)) $ go s1 s2
  where
    go (FObj x)      {-FObj-} y    = [(x, y)]
    go (FAbs _ t1)   (FAbs _ t2)   = go t1 t2
    go (FFunc s1 t1) (FFunc s2 t2) = go s1 s2 ++ go t1 t2
    go (FApp s1 t1)  (FApp s2 t2)  = go s1 s2 ++ go t1 t2
    go _             _             = []

--------------------------------------------------------------------------------
getEqBody :: Equation -> Maybe Expr
getEqBody (Equ x xts b _ _)
  | Just (fxs, e) <- getEqBodyPred b
  , (EVar f, es)  <- splitEApp fxs
  , f == x
  , es == (EVar . fst <$> xts)
  = Just e
getEqBody _
  = Nothing

getEqBodyPred :: Expr -> Maybe (Expr, Expr)
getEqBodyPred (PAtom Eq fxs e)
  = Just (fxs, e)
getEqBodyPred (PAnd ((PAtom Eq fxs e):_))
  = Just (fxs, e)
getEqBodyPred _
  = Nothing

eqArgNames :: Equation -> [Symbol]
eqArgNames = map fst . eqArgs

substPopIf :: [(Symbol, Expr)] -> Expr -> Expr
substPopIf xes e = L.foldl' go e xes
  where
    go e (x, EIte b e1 e2) = EIte b (subst1 e (x, e1)) (subst1 e (x, e2))
    go e (x, ex)           = subst1 e (x, ex)

evalRecApplication :: Knowledge -> Symbol -> CStack -> Expr -> Expr -> EvalST Expr
evalRecApplication γ _ stk e (EIte b e1 e2) = do
    b' <- eval γ stk b
    b1 <- liftIO (isValid γ b')
    if b1
     then addEquality γ e e1 >>
                   ({-# SCC "assertSelectors-1" #-} assertSelectors γ e1) >>
                   eval γ stk e1 >>=
                   ((e, "App1: ") ~>)
     else do
                   b2 <- liftIO (isValid γ (PNot b'))
                   if b2
                      then addEquality γ e e2 >>
                           ({-# SCC "assertSelectors-2" #-} assertSelectors γ e2) >>
                           eval γ stk (mytracepp ("evalREC-2: " ++ showpp stk) e2) >>=
                           ((e, ("App2: " ++ showpp stk ) ) ~>)
                      else return e
evalRecApplication γ f stk e bd = do 
  let alts  = splitBranches f bd
  altsEval <- mapM (\(c,e) -> (,e) <$> eval γ stk c) alts
  altsDec  <- liftIO $ mapM (\(c,e) -> (,e) <$> isValid γ c) altsEval  
  return $ Mb.fromMaybe e (snd <$> L.find fst altsDec)

splitBranches :: Symbol -> Expr -> [(Expr,Expr)]
splitBranches f = go 
  where 
    go (PAnd es) 
      | any (== f) (syms es) 
      = splitAnd <$> es
    go e         
      = [(PTrue,e)] 

    splitAnd (PImp c e) = (c,    e)
    splitAnd e          = (PTrue,e)
  

addEquality :: Knowledge -> Expr -> Expr -> EvalST ()
addEquality γ e1 e2 =
  modify (\st -> st{evSequence = (makeLam γ e1, makeLam γ e2):evSequence st})

evalIte :: Knowledge -> CStack -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ stk e b e1 e2 = mytracepp "evalIte:END: " <$> 
                            evalIteAc γ stk e b e1 (mytracepp msg e2) 
  where 
    msg = "evalIte:BEGINS: " ++ showpp (stk, e) 


evalIteAc :: Knowledge -> CStack -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIteAc γ stk e b e1 e2 
  = join $ evalIte' γ stk e b e1 e2 <$> liftIO (isValid γ b) <*> liftIO (isValid γ (PNot b))

evalIte' :: Knowledge -> CStack -> Expr -> Expr -> Expr -> Expr -> Bool -> Bool -> EvalST Expr
evalIte' γ stk e _ e1 _ b _
  | b
  = do e' <- eval γ stk e1
       (e, "If-True of:" ++ showpp b)  ~> e'
evalIte' γ stk e _ _ e2 _ b'
  | b'
  = do e' <- eval γ stk e2
       (e, "If-False") ~> e'
evalIte' γ stk _ b e1 e2 _ _
  -- see [NOTE:Eval-Ite] #387 
  = EIte b <$> eval γ stk' e1 <*> eval γ stk' e2 
    where stk' = mytracepp "evalIte'" $ noRecurCS stk 


--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge = KN 
  { knSims    :: ![Rewrite]           -- ^ Measure info, asserted for each new Ctor ('assertSelectors')
  , knAms     :: ![Equation]          -- ^ (Recursive) function definitions, used for PLE
  , knContext :: SMT.Context
  , knPreds   :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
  , knLams    :: [(Symbol, Sort)]
  , knSummary :: [(Symbol, Int)]
  }

isValid :: Knowledge -> Expr -> IO Bool
isValid γ e = do 
  contra <- knPreds γ (knContext γ) (knLams γ) PFalse
  if contra 
    then return False 
    else knPreds γ (knContext γ) (knLams γ) e

isProof :: (a, SortedReft) -> Bool 
isProof (_, RR s _) = showpp s == "Tuple"

knowledge :: Config -> SMT.Context -> SInfo a -> Knowledge
knowledge cfg ctx si = KN 
  { knSims    = sims 
  , knAms     = aenvEqs   aenv
  , knContext = ctx 
  , knPreds   = askSMT    cfg 
  , knLams    = [] 
  , knSummary =    ((\s -> (smName s, 1)) <$> sims) 
                ++ ((\s -> (eqName s, length (eqArgs s))) <$> aenvEqs aenv)
  } 
  where 
    sims = aenvSimpl aenv ++ concatMap reWriteDDecl (ddecls si) 
    aenv = ae si 

reWriteDDecl :: DataDecl -> [Rewrite]
reWriteDDecl ddecl = concatMap go' (ddCtors ddecl) -- ++
                     -- concatMap go (ddCtors ddecl)
  where 
    go' (DCtor f xs) =  sels {- 
    go (DCtor f xs)  = SMeasure (testSymbol f') f' ys PTrue:
                       ([SMeasure (testSymbol f') (symbol nf) (mkArg zs) PFalse | DCtor nf zs <- ddCtors ddecl, nf /= f ]  
                        ++ zipWith (\r i -> SMeasure r f' ys (EVar (ys!!i))) rs [0..]) -}
       where 
        sels = zipWith (\r i -> SMeasure r f' ys (EVar (ys!!i)) ) rs [0..]
        f'  = symbol f 
        rs  = (val . dfName) <$> xs  
        mkArg ws = zipWith (\_ i -> intSymbol (symbol ("darg"::String)) i) ws [0..]
        ys  = mkArg xs 




-- | This creates the rewrite rule e1 -> e2, applied when:
-- 1. when e2 is a DataCon and can lead to further reductions
-- 2. when size e2 < size e1
initEqualities :: SMT.Context -> AxiomEnv -> [(Symbol, SortedReft)] -> [(Expr, Expr)]
initEqualities ctx aenv es = concatMap (makeSimplifications (aenvSimpl aenv)) dcEqs
  where
    dcEqs                  = Misc.hashNub (Mb.catMaybes [getDCEquality senv e1 e2 | EEq e1 e2 <- atoms])
    atoms                  = splitPAnd =<< (expr <$> filter isProof es)
    senv                   = SMT.ctxSymEnv ctx

-- AT: Non-obvious needed invariant: askSMT True is always the 
-- totality-effecting one.
-- RJ: What does "totality effecting" mean? 

askSMT :: Config -> SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
askSMT cfg ctx bs e
  | isTautoPred  e     = return True
  | null (Vis.kvars e) = SMT.checkValidWithContext ctx [] PTrue e'
  | otherwise          = return False
  where 
    e'                 = toSMT cfg ctx bs e 

toSMT :: Config -> SMT.Context -> [(Symbol, Sort)] -> Expr -> Pred
toSMT cfg ctx bs = defuncAny cfg senv . elaborate "makeKnowledge" (elabEnv bs)
  where
    elabEnv      = insertsSymEnv senv
    senv         = SMT.ctxSymEnv ctx

makeSimplifications :: [Rewrite] -> (Symbol, [Expr], Expr) -> [(Expr, Expr)]
makeSimplifications sis (dc, es, e)
     = go =<< sis
 where
   go (SMeasure f dc' xs bd)
     | dc == dc', length xs == length es
     = [(EApp (EVar f) e, subst (mkSubst $ zip xs es) bd)]
   go _
     = []

getDCEquality :: SymEnv -> Expr -> Expr -> Maybe (Symbol, [Expr], Expr)
getDCEquality senv e1 e2
  | Just dc1 <- f1
  , Just dc2 <- f2
  = if dc1 == dc2
      then Nothing
      else error ("isDCEquality on" ++ showpp e1 ++ "\n" ++ showpp e2)
  | Just dc1 <- f1
  = Just (dc1, es1, e2)
  | Just dc2 <- f2
  = Just (dc2, es2, e1)
  | otherwise
  = Nothing
  where
    (f1, es1) = Misc.mapFst (getDC senv) (splitEApp e1)
    (f2, es2) = Misc.mapFst (getDC senv) (splitEApp e2)

-- TODO: Stringy hacks
getDC :: SymEnv -> Expr -> Maybe Symbol
getDC senv (EVar x)
  | isUpperSymbol x && Mb.isNothing (symEnvTheory x senv)
  = Just x
getDC _ _
  = Nothing

isUpperSymbol :: Symbol -> Bool
isUpperSymbol x = (0 < lengthSym x') && (isUpper $ headSym x')
  where 
    x' = dropModuleNames x 

dropModuleNames :: Symbol -> Symbol
dropModuleNames = mungeNames (symbol . last) "."
  where
    mungeNames _ _ ""  = ""
    mungeNames f d s'@(symbolText -> s)
      | s' == tupConName = tupConName
      | otherwise        = f $ T.splitOn d $ stripParens s
    stripParens t = Mb.fromMaybe t ((T.stripPrefix "(" >=> T.stripSuffix ")") t)

--------------------------------------------------------------------------------
-- | Creating Measure Info
--------------------------------------------------------------------------------
-- AT@TODO do this for all reflected functions, not just DataCons

{- [NOTE:Datacon-Selectors] The 'assertSelectors' function
   insert measure information for every constructor that appears
   in the expression e.

   In theory, this is not required as the SMT ADT encoding takes
   care of it. However, in practice, some constructors, e.g. from
   GADTs cannot be directly encoded in SMT due to the lack of SMTLIB
   support for GADT. Hence, we still need to hang onto this code.

   See tests/proof/ple2.fq for a concrete example.
 -}

assertSelectors :: Knowledge -> Expr -> EvalST ()
assertSelectors γ e = do
    sims <- aenvSimpl <$> gets _evAEnv
    -- cfg  <- gets evCfg
    -- _    <- foldlM (\_ s -> Vis.mapMExpr (go s) e) (mytracepp  "assertSelector" e) sims
    forM_ sims $ \s -> Vis.mapMExpr (go s) e
    return ()
  where
    go :: Rewrite -> Expr -> EvalST Expr
    go (SMeasure f dc xs bd) e@(EApp _ _)
      | (EVar dc', es) <- splitEApp e
      , dc == dc'
      , length xs == length es
      = do let e1 = EApp (EVar f) e
           let e2 = subst (mkSubst $ zip xs es) bd
           addEquality γ e1 e2
           return e
    go _ e
      = return e

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

(~>) :: (Expr, String) -> Expr -> EvalST Expr
(e, _str) ~> e' = do
  let msg = "PLE: " ++ _str ++ showpp (e, e') 
  modify (\st -> st {evId = (mytracepp msg $ evId st) + 1})
  return e'

-------------------------------------------------------------------------------
-- | Normalization of Equation: make their arguments unique -------------------
-------------------------------------------------------------------------------

class Normalizable a where 
  normalize :: a -> a 

instance Normalizable (GInfo c a) where 
  normalize si = si {ae = normalize $ ae si}

instance Normalizable AxiomEnv where 
  normalize aenv = aenv {aenvEqs = normalize <$> aenvEqs aenv}

instance Normalizable Equation where 
  normalize eq = eq {eqArgs = zip xs' ss, eqBody = subst su $ eqBody eq }
    where 
      su      = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      (xs,ss) = unzip (eqArgs eq) 
      xs'     = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (eqName eq) i 
