{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ExistentialQuantification #-}

--------------------------------------------------------------------------------
-- | Axiom Instantiation  ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Instantiate (instantiate) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config  as FC
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc -- (mapFst)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import qualified Language.Fixpoint.Utils.Trie    as T 
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Graph.Deps             (isTarget) 
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Control.Monad.State
import qualified Data.Text            as T
import qualified Data.HashMap.Strict  as M
import qualified Data.List            as L
import           Data.Maybe           (isNothing, catMaybes, fromMaybe)
import           Data.Char            (isUpper)
-- import           Text.Printf (printf)


(~>) :: (Expr, String) -> Expr -> EvalST Expr
(e, _str) ~> e' = do
  let msg = "PLE: " ++ _str ++ showpp (e, e') 
  modify (\st -> st {evId = (notracepp msg $ evId st) + 1})
  return e'

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instantiate :: (Loc a) => Config -> SInfo a -> IO (SInfo a)
instantiate cfg fi
  | False -- rewriteAxioms cfg 
  = instantiate' cfg fi
  | rewriteAxioms cfg -- False 
  = incrInstantiate' cfg fi
  | otherwise         
  = return fi

instantiate' :: (Loc a) => Config -> SInfo a -> IO (SInfo a)
instantiate' cfg fi = sInfo cfg env fi <$> withCtx cfg file env act
  where
    act ctx         = forM cstrs $ \(i, c) ->
                        ((i,srcSpan c),) . tracepp ("INSTANTIATE i = " ++ show i) <$> instSimpC cfg ctx (bs fi) aenv i c
    cstrs           = [ (i, c) | (i, c) <- M.toList (cm fi) , isPleCstr aenv i c] 
    file            = srcFile cfg ++ ".evals"
    env             = symbolEnv cfg fi
    aenv            = {- notracepp "AXIOM-ENV" -} (ae fi)


sInfo :: Config -> SymEnv -> SInfo a -> [((SubcId, SrcSpan), Expr)] -> SInfo a
sInfo cfg env fi ips = strengthenHyp fi' (notracepp "ELAB-INST:  " $ zip (fst <$> is) ps'')
  where
    (is, ps)         = unzip ips
    (ps', axs)       = defuncAxioms cfg env ps
    ps''             = zipWith (\(i, sp) -> elaborate (atLoc sp ("PLE1 " ++ show i)) env) is ps' 
    axs'             = elaborate (atLoc dummySpan "PLE2") env <$> axs
    fi'              = fi { asserts = axs' ++ asserts fi }

incrInstantiate' :: (Loc a) => Config -> SInfo a -> IO (SInfo a)
incrInstantiate' cfg fi = do 
    res   <- withCtx cfg file sEnv (trieResult t . instEnv cfg fi cs)
    return $ incrSInfo cfg sEnv fi res 
  where
    t      = mkCTrie cs
    cs     = [ (i, c) | (i, c) <- M.toList (cm fi), isPleCstr aEnv i c ] 
    file   = srcFile cfg ++ ".evals"
    sEnv   = symbolEnv cfg fi
    aEnv   = ae fi 


instEnv :: (Loc a) => Config -> SInfo a -> [(SubcId, SimpC a)] -> SMT.Context -> InstEnv a 
instEnv cfg fi cs ctx = InstEnv cfg ctx bEnv aEnv (M.fromList cs) 
  where 
    bEnv              = bs fi
    aEnv              = ae fi

-- instT :: InstEnv a -> CTrie -> IO InstRes

incrSInfo :: Config -> SymEnv -> SInfo a -> InstRes -> SInfo a
incrSInfo cfg env fi res = strengthenBinds fi' res' 
  where
    res'                 = M.fromList $ notracepp "ELAB-INST:  " $ zip is ps''
    ps''                 = zipWith (\i -> elaborate (atLoc dummySpan ("PLE1 " ++ show i)) env) is ps' 
    (ps', axs)           = defuncAxioms cfg env ps
    (is, ps)             = unzip (M.toList res)
    axs'                 = elaborate (atLoc dummySpan "PLE2") env <$> axs
    fi'                  = fi { asserts = axs' ++ asserts fi }


withCtx :: Config -> FilePath -> SymEnv -> (SMT.Context -> IO a) -> IO a
withCtx cfg file env k = do
  ctx <- SMT.makeContextWithSEnv cfg file env
  _   <- SMT.smtPush ctx
  res <- k ctx
  _   <- SMT.cleanupContext ctx
  return res

------------------------------------------------------------------------------- 
-- | "Incremental" PLE
------------------------------------------------------------------------------- 

data InstEnv a = InstEnv 
  { _ieCfg  :: !Config
  , _ieSMT  :: !SMT.Context
  , ieBEnv  :: !BindEnv
  , ieAenv  :: !AxiomEnv 
  , ieCstrs :: !(M.HashMap SubcId (SimpC a))
  } 

type InstRes = M.HashMap BindId Expr
type CTrie   = T.Trie   SubcId
type CBranch = T.Branch SubcId
type Assumes = [Expr]     -- ultimately, the SMT context 
type Diff    = [BindId]   -- ^ in "reverse" order

trieResult :: CTrie -> InstEnv a -> IO InstRes
trieResult t env = loopT env ctx0 diff0 Nothing res0 t 
  where 
    diff0        = []
    res0         = M.empty 
    ctx0         = updCtx [] e0
    e0           = pAnd $ eqBody <$> L.filter (null . eqArgs) (aenvEqs . ieAenv $ env) -- formerly is0 

loopT :: InstEnv a -> Assumes -> Diff -> Maybe BindId -> InstRes -> CTrie -> IO InstRes
loopT env ctx delta i res t = case t of 
  T.Node []  -> return res
  T.Node [b] -> loopB env ctx delta i res b
  T.Node bs  -> do e'      <- ple1 env ctx delta i Nothing
                   let ctx' = updCtx ctx e'
                   let res' = updRes res i e'
                   foldM (loopB env ctx' [] i) res' bs

loopB :: InstEnv a -> Assumes -> Diff -> Maybe BindId -> InstRes -> CBranch -> IO InstRes
loopB env ctx delta _ res (T.Bind i t) = 
  loopT env ctx (i:delta) (Just i) res t
loopB env ctx delta i res (T.Val cid)  = do 
  e' <- ple1 env ctx delta i (Just cid)
  return (updRes res i e')


ple1 :: InstEnv a -> Assumes -> Diff -> Maybe BindId -> Maybe SubcId -> IO Expr 
ple1 env ctx delta i cidMb = incrInstSimpC env ctx delta (getCstr <$> tracepp msg cidMb)
  where 
    msg                    = "PLE-1: " ++ show i 
    getCstr cid            = Misc.safeLookup "Instantiate.getCstr" cid (ieCstrs env)

updRes :: InstRes -> Maybe BindId -> Expr -> InstRes
updRes res (Just i) e = M.insert i e res 
updRes res  Nothing _ = res 

updCtx :: Assumes -> Expr -> Assumes 
updCtx es e = e:es 

mkCTrie :: [(SubcId, SimpC a)] -> CTrie 
mkCTrie ics  = Misc.traceShow "TRIE:" $ T.fromList [ (cBinds c, i) | (i, c) <- ics ]
  where
    cBinds   = L.sort . elemsIBindEnv . senv 

--------------------------------------------------------------------------------
-- | PLE for a single 'SimpC'
--------------------------------------------------------------------------------
incrInstSimpC :: InstEnv a -> Assumes -> Diff -> Maybe (SimpC a) -> IO Expr
--------------------------------------------------------------------------------
incrInstSimpC env ps delta subMb = do
  let (bs, es0) = incrCstrExprs (ieBEnv env) delta subMb
  equalities   <- incrEval env ps bs es0 
  let evalEqs   = [ EEq e1 e2 | (e1, e2) <- equalities, e1 /= e2 ] 
  return        $ pAnd evalEqs  

{- 
incrCstrExprs :: BindEnv -> Diff -> Maybe (SimpC a) -> ([(Symbol, SortedReft)], [Expr])
incrCstrExprs benv diff subMb = (unElab <$> binds, unElab <$> es)
  where
    es                        = eRhs : (expr <$> binds)
    eRhs                      = maybe PTrue crhs subMb
    binds                     = [ lookupBindEnv i benv | i <- diff ] 
-}

{- |  [NOTE:Incremental-PLE] 
      1. At an "internal" branch point within the trie, there is no RHS
      2. At an "external" leaf, if the "diff" is a singleton then it is just the LHS bind,
         and any interesting PLE-candidates are already in the environment. 
  -} 

incrCstrExprs :: BindEnv -> Diff -> Maybe (SimpC a) -> ([(Symbol, SortedReft)], [Expr])
incrCstrExprs benv diff Nothing = (unElab <$> binds, unElab <$> es)
  where
    es                          = expr <$> binds
    binds                       = [ lookupBindEnv i benv | i <- diff ] 

incrCstrExprs benv diff (Just c) = (unElab <$> binds, unElab <$> es)
  where
    es                           = (crhs c) : (expr <$> binds)
    binds                        = [ lookupBindEnv i benv | i <- drop (tracepp msg 1) diff ] 
    msg                          = "incrCstrExprs: " ++ show (sid c, diff)
    


--------------------------------------------------------------------------------
instSimpC :: Config -> SMT.Context -> BindEnv -> AxiomEnv
          -> SubcId 
          -> SimpC a 
          -> IO Expr
--------------------------------------------------------------------------------
instSimpC cfg ctx bds aenv sid sub 
  | isPleCstr aenv sid sub = do
    let is0       = eqBody <$> L.filter (null . eqArgs) (aenvEqs aenv) 
    let (bs, es0) = cstrExprs bds sub
    equalities   <- evaluate cfg ctx aenv bs es0 
    let evalEqs   = [ EEq e1 e2 | (e1, e2) <- equalities, e1 /= e2 ] 
    return        $ pAnd (is0 ++ evalEqs)  
  | otherwise     = return PTrue

isPleCstr :: AxiomEnv -> SubcId -> SimpC a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 

cstrExprs :: BindEnv -> SimpC a -> ([(Symbol, SortedReft)], [Expr])
cstrExprs bds sub = (unElab <$> binds, unElab <$> es)
  where
    es            = (crhs sub) : (expr <$> binds)
    binds         = envCs bds (senv sub)

unElab :: (Vis.Visitable t) => t -> t
unElab = Vis.stripCasts . unApply

unApply :: (Vis.Visitable t) => t -> t
unApply = Vis.trans (Vis.defaultVisitor { Vis.txExpr = const go }) () ()
  where
    go (ECst (EApp (EApp f e1) e2) _)
      | Just _ <- unApplyAt f = EApp e1 e2
    go e                      = e


--------------------------------------------------------------------------------
-- | Symbolic Evaluation with SMT
--------------------------------------------------------------------------------
incrEval :: InstEnv a -- Config -> SMT.Context -> AxiomEnv -- ^ Definitions
         -> Assumes                   -- ^ Known facts
         -> [(Symbol, SortedReft)]    -- ^ "Diff" binders to use as candidates
         -> [Expr]                    -- ^ Candidates for unfolding 
         -> IO [(Expr, Expr)]         -- ^ Newly unfolded equalities
--------------------------------------------------------------------------------
incrEval (InstEnv cfg ctx _ aenv _) ps facts eCands = do 
  eqss    <- evalCands ctx ctxEqs γ s0 cands
  return   $ eqs ++ concat eqss
  where 
    γ      = knowledge cfg ctx aenv 
    eqs    = initEqualities ctx aenv facts  
    cands  = tracepp "evaluate: cands" $ Misc.hashNub (concatMap topApps eCands)
    s0     = EvalEnv 0 [] aenv (SMT.ctxSymEnv ctx) cfg
    ctxEqs = toSMT cfg ctx [] <$> concat 
                [ ps
                , [ EEq e1 e2 | (e1, e2)  <- eqs ]
                , [ expr xr   | xr@(_, r) <- facts, null (Vis.kvars r) ] 
                ]

evalCands :: SMT.Context -> [Expr] -> Knowledge -> EvalEnv -> [Expr] -> IO [[(Expr, Expr)]]
evalCands _   _      _ _  []    = return []
evalCands ctx ctxEqs γ s0 cands = SMT.smtBracket ctx "PLE.evaluate" $ do
                                    forM_ ctxEqs (SMT.smtAssert ctx) 
                                    mapM (evalOne γ s0) cands
 
--------------------------------------------------------------------------------
evaluate :: Config -> SMT.Context -> AxiomEnv -- ^ Definitions
         -> [(Symbol, SortedReft)]            -- ^ Environment of "true" facts 
         -> [Expr]                            -- ^ Candidates for unfolding 
         -> IO [(Expr, Expr)]                 -- ^ Newly unfolded equalities
--------------------------------------------------------------------------------
evaluate cfg ctx aenv facts es = do 
  let eqs      = initEqualities ctx aenv facts  
  let γ        = knowledge cfg ctx aenv 
  let cands    = notracepp "evaluate: cands" $ Misc.hashNub (concatMap topApps es)
  let s0       = EvalEnv 0 [] aenv (SMT.ctxSymEnv ctx) cfg
  let ctxEqs   = [ toSMT cfg ctx [] (EEq e1 e2) | (e1, e2)  <- eqs ]
              ++ [ toSMT cfg ctx [] (expr xr)   | xr@(_, r) <- facts, null (Vis.kvars r) ] 
  eqss        <- SMT.smtBracket ctx "PLE.evaluate" $ do
                   forM_ ctxEqs (SMT.smtAssert ctx) 
                   mapM (evalOne γ s0) cands
  return        $ eqs ++ concat eqss


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

evalOne :: Knowledge -> EvalEnv -> Expr -> IO [(Expr, Expr)]
evalOne γ s0 e = do
  (e', st) <- runStateT (eval γ e) s0 
  if e' == e then return [] else return ((e, e') : evSequence st)

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
    go e@(EApp _ _)    = [e]
    go _               = []

-- makeLam is the adjoint of splitEApp
makeLam :: Knowledge -> Expr -> Expr
makeLam γ e = L.foldl' (flip ELam) e (knLams γ)

eval :: Knowledge -> Expr -> EvalST Expr
eval γ (ELam (x,s) e)
  = do e'    <- eval γ{knLams = (x, s) : knLams γ} e
       return $ ELam (x, s) e'

eval γ e@(EIte b e1 e2)
  = do b' <- eval γ b
       evalIte γ e b' e1 e2
eval γ (ECoerc s t e)
  = ECoerc s t <$> eval γ e
eval γ e@(EApp _ _)
  = evalArgs γ e >>= evalApp γ e
eval γ e@(EVar _)
  = evalApp γ e (e,[])
eval γ (PAtom r e1 e2)
  = PAtom r <$> eval γ e1 <*> eval γ e2
eval γ (ENeg e)
  = ENeg <$> eval γ e
eval γ (EBin o e1 e2)
  = EBin o <$> eval γ e1 <*> eval γ e2
eval γ (ETApp e t)
  = flip ETApp t <$> eval γ e
eval γ (ETAbs e s)
  = flip ETAbs s <$> eval γ e
eval γ (PNot e)
  = PNot <$> eval γ e
eval γ (PImp e1 e2)
  = PImp <$> eval γ e1 <*> eval γ e2
eval γ (PIff e1 e2)
  = PIff <$> eval γ e1 <*> eval γ e2
eval γ (PAnd es)
  = PAnd <$> (eval γ <$$> es)
eval γ (POr es)
  = POr  <$> (eval γ <$$> es)
eval _ e = return e

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs


evalArgs :: Knowledge -> Expr -> EvalST (Expr, [Expr])
evalArgs γ = go []
  where
    go acc (EApp f e)
      = do f' <- eval γ f
           e' <- eval γ e
           go (e':acc) f'
    go acc e
      = (,acc) <$> eval γ e

evalApp :: Knowledge -> Expr -> (Expr, [Expr]) -> EvalST Expr
evalApp γ e (EVar f, [ex])
  | (EVar dc, es) <- splitEApp ex
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (knSims γ)
  , length (smArgs simp) == length es
  = do e'    <- eval γ $ substPopIf (zip (smArgs simp) es) (smBody simp)
       (e, "Rewrite -" ++ showpp f) ~> e'
evalApp γ _ (EVar f, es)
  -- we should move the lookupKnowledge stuff here into kmAms γ
  | Just eq <- L.find (( == f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es
  , f `notElem` syms bd               -- non-recursive equations
  = do env   <- seSort <$> gets evEnv
       let ee = substEq env PopIf eq es bd
       assertSelectors γ ee 
       eval γ ee 

evalApp γ _e (EVar f, es)
  | Just eq <- L.find ((== f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es   -- recursive equations
  = do env      <- seSort <$> gets evEnv
       evalRecApplication γ (eApps (EVar f) es) (substEq env Normal eq es bd)
evalApp _ _ (f, es)
  = return $ eApps f es

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
    coSub = notracepp ("substEqCoerce" ++ showpp (eqName eq, es, eTs, ts)) $ mkCoSub eTs ts

mkCoSub :: [Sort] -> [Sort] -> Vis.CoSub
mkCoSub eTs xTs = Misc.safeFromList "mkCoSub" xys
  where
    xys         = concat (zipWith matchSorts xTs eTs)

matchSorts :: Sort -> Sort -> [(Symbol, Sort)]
matchSorts s1 s2 = notracepp ("matchSorts :" ++ show (s1, s2)) $ go s1 s2
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

evalRecApplication :: Knowledge -> Expr -> Expr -> EvalST Expr
evalRecApplication γ e (EIte b e1 e2) = do
  contra <- {- notracepp ("CONTRA? " ++ showpp e) <$> -} liftIO (isValid γ PFalse)
  if contra
    then return e
    else do b' <- eval γ b
            b1 <- liftIO (isValid γ b')
            if b1
              then addEquality γ e e1 >>
                   ({-# SCC "assertSelectors-1" #-} assertSelectors γ e1) >>
                   eval γ e1 >>=
                   ((e, "App1: ") ~>)
              else do
                   b2 <- liftIO (isValid γ (PNot b'))
                   if b2
                      then addEquality γ e e2 >>
                           ({-# SCC "assertSelectors-2" #-} assertSelectors γ e2) >>
                           eval γ e2 >>=
                           ((e, "App2: ") ~>)
                      else return e
evalRecApplication _ _ e
  = return e

addEquality :: Knowledge -> Expr -> Expr -> EvalST ()
addEquality γ e1 e2 =
  modify (\st -> st{evSequence = (makeLam γ e1, makeLam γ e2):evSequence st})

evalIte :: Knowledge -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ e b e1 e2 = join $
                      evalIte' γ e b e1 e2 <$>
                      liftIO (isValid γ b) <*>
                      liftIO (isValid γ (PNot b))

evalIte' :: Knowledge -> Expr -> Expr -> Expr -> Expr -> Bool -> Bool
            -> EvalST Expr
evalIte' γ e _ e1 _ b _
  | b
  = do e' <- eval γ e1
       (e, "If-True of:" ++ showpp b)  ~> e'
evalIte' γ e _ _ e2 _ b'
  | b'
  = do e' <- eval γ e2
       (e, "If-False") ~> e'
evalIte' γ _ b e1 e2 _ _
  = do e1' <- eval γ e1
       e2' <- eval γ e2
       return $ EIte b e1' e2'

instance Expression (Symbol, SortedReft) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)

--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge = KN 
  { knSims    :: ![Rewrite]           -- ^ Measure info, asserted for each new Ctor ('assertSelectors')
  , knAms     :: ![Equation]          -- ^ (Recursive) function definitions, used for PLE
  , knContext :: SMT.Context
  , knPreds   :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
  , knLams    :: [(Symbol, Sort)]
  }

isValid :: Knowledge -> Expr -> IO Bool
isValid γ e = knPreds γ (knContext γ) (knLams γ) e

isProof :: (a, SortedReft) -> Bool 
isProof (_, RR s _) = showpp s == "Tuple"

knowledge :: Config -> SMT.Context -> AxiomEnv -> Knowledge
knowledge cfg ctx aenv = KN 
  { knSims    = aenvSimpl aenv
  , knAms     = aenvEqs   aenv
  , knContext = ctx 
  , knPreds   = askSMT    cfg 
  , knLams    = [] 
  } 

-- | This creates the rewrite rule e1 -> e2, applied when:
-- 1. when e2 is a DataCon and can lead to further reductions
-- 2. when size e2 < size e1

initEqualities :: SMT.Context -> AxiomEnv -> [(Symbol, SortedReft)] -> [(Expr, Expr)]
initEqualities ctx aenv es = simpleEqs
  where
    simpleEqs              = concatMap (makeSimplifications (aenvSimpl aenv)) dcEqs
    dcEqs                  = Misc.hashNub (catMaybes [getDCEquality senv e1 e2 | EEq e1 e2 <- atoms])
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
    elabEnv      = L.foldl' (\env (x, s) -> insertSymEnv x s env) senv
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
  | isUpperSymbol x && isNothing (symEnvTheory x senv)
  = Just x
getDC _ _
  = Nothing

isUpperSymbol :: Symbol -> Bool
isUpperSymbol = isUpper . headSym . dropModuleNames

dropModuleNames :: Symbol -> Symbol
dropModuleNames = mungeNames (symbol . last) "."
  where
    mungeNames _ _ ""  = ""
    mungeNames f d s'@(symbolText -> s)
      | s' == tupConName = tupConName
      | otherwise        = f $ T.splitOn d $ stripParens s

    stripParens t = fromMaybe t ((T.stripPrefix "(" >=> T.stripSuffix ")") t)

splitPAnd :: Expr -> [Expr]
splitPAnd (PAnd es) = concatMap splitPAnd es
splitPAnd e         = [e]

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
    -- _    <- foldlM (\_ s -> Vis.mapMExpr (go s) e) (notracepp "assertSelector" e) sims
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
