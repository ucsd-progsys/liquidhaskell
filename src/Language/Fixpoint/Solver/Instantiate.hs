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

module Language.Fixpoint.Solver.Instantiate (
  instantiate
  ) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config  as FC
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc -- (mapFst)
import           Language.Fixpoint.Misc          ((<<=))
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import           Language.Fixpoint.SortCheck
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
  modify (\st -> st {evId = (tracepp msg $ evId st) + 1})
  return e'

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instantiate :: Config -> SInfo a -> IO (SInfo a)
instantiate cfg fi
  | rewriteAxioms cfg = instantiate' cfg fi
  | otherwise         = return fi

instantiate' :: Config -> GInfo SimpC a -> IO (SInfo a)
instantiate' cfg fi = sInfo cfg fi env <$> withCtx cfg file env act
  where
    act ctx         = forM cstrs $ \(i, c) ->
                        (i,) . notracepp ("INSTANTIATE i = " ++ show i) <$> instSimpC cfg ctx (bs fi) aenv i c
    cstrs           = M.toList (cm fi)
    file            = srcFile cfg ++ ".evals"
    env             = symbolEnv cfg fi
    aenv            = {- tracepp "AXIOM-ENV" -} (ae fi)

sInfo :: Config -> GInfo SimpC a -> SymEnv -> [(SubcId, Expr)] -> SInfo a
sInfo cfg fi env ips = strengthenHyp fi' (notracepp "ELAB-INST:  " $ zip is ps'')
  where
    (is, ps)         = unzip ips
    (ps', axs)       = defuncAxioms cfg env ps
    ps''             = zipWith (\i -> elaborate ("PLE1 " ++ show i) env) is ps' -- <$> ps'
    axs'             = elaborate "PLE2" env <$> axs
    fi'              = fi { asserts = axs' ++ asserts fi }

withCtx :: Config -> FilePath -> SymEnv -> (SMT.Context -> IO a) -> IO a
withCtx cfg file env k = do
  ctx <- SMT.makeContextWithSEnv cfg file env
  _   <- SMT.smtPush ctx
  res <- k ctx
  _   <- SMT.cleanupContext ctx
  return res


--------------------------------------------------------------------------------
-- | Partition Binds into individual "owning" constraints, to not repeat PLE 
--   for each bind, but instead, to just do PLE for that bind while at the 
--   the "root" constraint.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | PLE for a single 'SimpC'
--------------------------------------------------------------------------------
instSimpC :: Config -> SMT.Context -> BindEnv -> AxiomEnv
          -> Integer -> SimpC a 
          -> IO Expr
--------------------------------------------------------------------------------
instSimpC cfg ctx bds aenv sid sub 
  | not (M.lookupDefault False sid (aenvExpand aenv)) = 
    return PTrue
  | otherwise                                         = do
    let is0       = eqBody <$> L.filter (null . eqArgs) (aenvEqs aenv) 
    let (bs, es0) = cstrExprs bds sub
    equalities   <- evaluate cfg ctx bs aenv es0 
    let evalEqs   = [ EEq e1 e2 | (e1, e2) <- equalities, e1 /= e2 ] 
    return        $ pAnd (is0 ++ evalEqs)  

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
    -- _    <- foldlM (\_ s -> Vis.mapMExpr (go s) e) (tracepp "assertSelector" e) sims
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
-- | Symbolic Evaluation with SMT
--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evId        :: !Int
  , evSequence  :: [(Expr,Expr)]
  , _evAEnv     :: !AxiomEnv
  , evEnv       :: !SymEnv
  , _evCfg      :: !Config
  }

type EvalST a = StateT EvalEnv IO a

evaluate :: Config -> SMT.Context -> [(Symbol, SortedReft)] -> AxiomEnv -> [Expr] 
         -> IO [(Expr, Expr)]
evaluate cfg ctx facts aenv es = do 
  let eqs      = initEqualities ctx aenv facts  
  let γ        = knowledge cfg ctx aenv 
  let cands    = Misc.hashNub (concatMap topApps es)
  let s0       = EvalEnv 0 [] aenv (SMT.ctxSymEnv ctx) cfg
  let ctxEqs   = [ toSMT cfg ctx [] (EEq e1 e2) | (e1, e2)  <- eqs ]
              ++ [ toSMT cfg ctx [] (expr xr)   | xr@(_, r) <- facts, null (Vis.kvars r) ] 
  eqss        <- SMT.smtBracket ctx "PLE.evaluate" $ do
                   forM_ ctxEqs (SMT.smtAssert ctx) 
                   mapM (evalOne γ s0) cands
  return        $ eqs ++ concat eqss

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
  = eval γ =<< assertSelectors γ <<= substEq PopIf eq es bd

evalApp γ _e (EVar f, es)
  | Just eq <- L.find ((== f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es   -- recursive equations
  = evalRecApplication γ (eApps (EVar f) es) =<< substEq Normal eq es bd
evalApp _ _ (f, es)
  = return $ eApps f es

--------------------------------------------------------------------------------
-- | 'substEq' unfolds or instantiates an equation at a particular list of
--   argument values. We must also substitute the sort-variables that appear
--   as coercions. See tests/proof/ple1.fq
--------------------------------------------------------------------------------
substEq :: SubstOp -> Equation -> [Expr] -> Expr -> EvalST Expr
substEq o eq es bd = substEqVal o eq es <$> substEqCoerce eq es bd

data SubstOp = PopIf | Normal

substEqVal :: SubstOp -> Equation -> [Expr] -> Expr -> Expr
substEqVal o eq es bd = case o of
    PopIf  -> substPopIf     xes  bd
    Normal -> subst (mkSubst xes) bd
  where
    xes    =  zip xs es
    xs     =  eqArgNames eq

substEqCoerce :: Equation -> [Expr] -> Expr -> EvalST Expr
substEqCoerce eq es bd = do
  env      <- seSort <$> gets evEnv
  let ts    = snd    <$> eqArgs eq
  let sp    = panicSpan "mkCoSub"
  let eTs   = sortExpr sp env <$> es
  let coSub = notracepp ("substEqCoerce" ++ showpp (eqName eq, es, eTs, ts)) $ mkCoSub eTs ts
  return    $ Vis.applyCoSub coSub bd

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
  contra <- {- tracepp ("CONTRA? " ++ showpp e) <$> -} liftIO (isValid γ PFalse)
  if contra
    then return e
    else do b' <- eval γ b
            b1 <- liftIO (isValid γ b')
            if b1
              then addEquality γ e e1 >>
                   ({-# SCC "assertSelectors-1" #-} assertSelectors γ e1) >>
                   eval γ e1 >>=
                   ((e, "App") ~>)
              else do
                   b2 <- liftIO (isValid γ (PNot b'))
                   if b2
                      then addEquality γ e e2 >>
                           ({-# SCC "assertSelectors-2" #-} assertSelectors γ e2) >>
                           eval γ e2 >>=
                           ((e, "App") ~>)
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