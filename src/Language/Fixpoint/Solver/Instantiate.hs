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
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Control.Monad.State

-- AT: I've inlined this, but we should have a more elegant solution
--     (track predicates instead of selectors!)
-- import           Language.Haskell.Liquid.GHC.Misc (dropModuleNames)
import qualified Data.Text            as T
import qualified Data.HashMap.Strict  as M
import qualified Data.List            as L
import           Data.Maybe           (catMaybes, fromMaybe)
import           Data.Char            (isUpper)
-- import           Data.Foldable        (foldlM)

(~>) :: (Expr, String) -> Expr -> EvalST Expr
(_e,_str) ~> e' = do
    modify (\st -> st{evId = evId st + 1})
    -- traceM $ showpp _str ++ " : " ++ showpp _e ++ showpp e'
    return (η e')


--------------------------------------------------------------------------------
-- | Instantiate Axioms
--------------------------------------------------------------------------------
instantiate :: Config -> SInfo a -> IO (SInfo a)
instantiate cfg fi
  | rewriteAxioms cfg = instantiate' cfg fi
  | otherwise = return fi

-- instantiate' :: Config -> SInfo a -> IO (SInfo a)
-- instantiate' cfg fi = do
    -- ctx <- SMT.makeContextWithSEnv cfg file env
    -- -- ctx <- SMT.makeSmtContext cfg file (ddecls fi) [] (applySorts fi)
    -- SMT.smtPush ctx
    -- ips <- forM cstrs $ \(i, c) -> do
             -- p <- instSimpC cfg ctx (bs fi) (ae fi) i c
             -- return (i, elaborate "PLE-instantiate" env p)
    -- return (strengthenHyp fi ips)

instantiate' :: Config -> GInfo SimpC a -> IO (SInfo a)
instantiate' cfg fi = sInfo cfg fi env <$> withCtx cfg file env act
  where
    act ctx         = forM cstrs $ \(i, c) ->
                        (i,) {- . tracepp ("INSTANTIATE i = " ++ show i) -} <$> instSimpC cfg ctx (bs fi) (ae fi) i c
    cstrs           = M.toList (cm fi)
    file            = srcFile cfg ++ ".evals"
    env             = symbolEnv cfg fi

sInfo :: Config -> GInfo SimpC a -> SymEnv -> [(SubcId, Expr)] -> SInfo a
sInfo cfg fi env ips = strengthenHyp fi' (zip is ps'')
  where
    (is, ps)         = unzip ips
    (ps', axs)       = defuncAxioms cfg env ps
    ps''             = elaborate "PLE1" env <$> ps'
    axs'             = elaborate "PLE2" env <$> axs
    fi'              = fi { asserts = axs' ++ asserts fi }

withCtx :: Config -> FilePath -> SymEnv -> (SMT.Context -> IO a) -> IO a
withCtx cfg file env k = do
  ctx <- SMT.makeContextWithSEnv cfg file env
  _   <- SMT.smtPush ctx
  res <- k ctx
  _   <- SMT.cleanupContext ctx
  return res

instSimpC :: Config -> SMT.Context -> BindEnv -> AxiomEnv
          -> Integer -> SimpC a
          -> IO Expr
instSimpC _ _ _ aenv sid _
  | not (M.lookupDefault False sid (aenvExpand aenv))
  = return PTrue
instSimpC cfg ctx bds aenv _ sub
  = -- tracepp ("instSimpC " ++ show sid) .
    pAnd . (is0 ++) <$>
    if rewriteAxioms cfg then evalEqs else return []
  where
    is0              = eqBody <$> L.filter (null . eqArgs) eqs
    evalEqs          =
       map (uncurry (PAtom Eq)) .
       filter (uncurry (/=)) <$>
       evaluate cfg ctx ({- (vv Nothing, slhs sub): -} binds) aenv iExprs
    eqs              = aenvEqs aenv
    (binds, iExprs)  = cstrBindExprs bds sub

cstrBindExprs :: BindEnv -> SimpC a -> ([(Symbol, SortedReft)], [Expr])
cstrBindExprs bds sub = {- tracepp "initExpressions" -} (unElab <$> binds, unElab <$> es)
  where
    es                = {- expr (slhs sub) : -} (crhs sub) : (expr <$> binds)
    binds             = envCs bds (senv sub)
  --   _tx e              = tracepp ("UNELAB e = " ++ showpp e) (unElab e)

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
-- AT:@TODO: knSels and knEqs should really just be the same thing. In this way,
-- we should also unify knSims and knAms, as well as their analogues in AxiomEnv
data Knowledge
  = KN { knSels    :: ![(Expr, Expr)]
       , knEqs     :: ![(Expr, Expr)]
       , knSims    :: ![Rewrite]
       , knAms     :: ![Equation]
       , knContext :: IO SMT.Context
       , knPreds   :: !([(Symbol, Sort)] -> Expr -> SMT.Context -> IO Bool)
       , knLams    :: [(Symbol, Sort)]
       }

emptyKnowledge :: IO SMT.Context -> Knowledge
emptyKnowledge ctx = KN [] [] [] [] ctx (\_ _ _ -> return False) []

lookupKnowledge :: Knowledge -> Expr -> Maybe Expr
lookupKnowledge γ e
  -- Zero argument axioms like `mempty = N`
  | Just e' <- L.lookup e (knEqs γ)
  = Just e'
  | Just e' <- L.lookup e (knSels γ)
  = Just e'
  | otherwise
  = Nothing

isValid :: Knowledge -> Expr -> IO Bool
isValid γ b = knPreds γ (knLams γ) b =<< knContext γ

makeKnowledge :: Config -> SMT.Context -> AxiomEnv
                 -> [(Symbol, SortedReft)]
                 -> ([(Expr, Expr)], Knowledge)
makeKnowledge cfg ctx aenv es = (simpleEqs,) $ (emptyKnowledge context)
                                     { knSels   = sels
                                     , knEqs    = eqs
                                     , knSims   = aenvSimpl aenv
                                     , knAms    = aenvEqs aenv
                                     , knPreds  = \bs e c -> askSMT c bs e
                                     }
  where
    senv = SMT.ctxSymEnv ctx
    context :: IO SMT.Context
    context = do
      SMT.smtPop ctx
      SMT.smtPush ctx
      -- SMT.smtDecls ctx $ L.nub [(x, toSMT [] s) | (x, s) <- fbinds, not (memberSEnv x thySyms)]
      SMT.smtAssert ctx (pAnd ([toSMT [] (PAtom Eq e1 e2) | (e1, e2) <- simpleEqs]
                               ++ filter (null . Vis.kvars) ((toSMT [] . expr) <$> es)
                              ))
      return ctx

    -- This creates the rewrite rule e1 -> e2
    -- when should I apply it?
    -- 1. when e2 is a data con and can lead to further reductions
    -- 2. when size e2 < size e1
    -- @TODO: Can this be generalized?
    -- simpleEqs = []
    simpleEqs = {- tracepp "SIMPLEEQS" $ -} _makeSimplifications (aenvSimpl aenv) =<<
               L.nub (catMaybes [_getDCEquality e1 e2 | PAtom Eq e1 e2 <- atms])
    atms = splitPAnd =<< (expr <$> filter isProof es)
    isProof (_, RR s _) = showpp s == "Tuple"
    sels = (go . expr) =<< es
    go e = let es   = splitPAnd e
               su   = mkSubst [(x, EVar y)  | PAtom Eq (EVar x) (EVar y) <- es ]
               sels = [(EApp (EVar s) x, e) | PAtom Eq (EApp (EVar s) x) e <- es
                                            , isSelector s ]
           in L.nub (sels ++ subst su sels)

    eqs = [(EVar x, ex) | Equ a _ bd <- filter (null . eqArgs) $ aenvEqs aenv
                        , PAtom Eq (EVar x) ex <- splitPAnd bd
                        , x == a
                        ]

    toSMT bs = defuncAny cfg senv . elaborate "makeKnowledge" (elabEnv bs)
    elabEnv  = L.foldl' (\env (x, s) -> insertSymEnv x s env) senv

    -- AT: Non-obvious needed invariant: askSMT True is always the
    -- totality-effecting one
    askSMT :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
    askSMT ctx bs e
      | isTautoPred  e = return True
      | isContraPred e = return False
      | null (Vis.kvars e) = do
          SMT.smtPush ctx
          b <- SMT.checkValid' ctx [] PTrue (toSMT bs e)
          SMT.smtPop ctx
          return b
      | otherwise      = return False

    -- TODO: Stringy hacks
    isSelector :: Symbol -> Bool
    isSelector  = L.isPrefixOf "select" . symbolString

_makeSimplifications :: [Rewrite] -> (Symbol, [Expr], Expr) -> [(Expr, Expr)]
_makeSimplifications sis (dc, es, e)
 = go =<< sis
 where
   go (SMeasure f dc' xs bd)
     | dc == dc', length xs == length es
     = [(EApp (EVar f) e, subst (mkSubst $ zip xs es) bd)]
   go _
     = []

_getDCEquality :: Expr -> Expr -> Maybe (Symbol, [Expr], Expr)
_getDCEquality e1 e2
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
    (f1, es1) = Misc.mapFst getDC $ splitEApp e1
    (f2, es2) = Misc.mapFst getDC $ splitEApp e2

    -- TODO: Stringy hacks
    getDC (EVar x)
      = if isUpper $ head $ symbolString $ dropModuleNames x
          then Just x
          else Nothing
    getDC _
      = Nothing

    dropModuleNames = mungeNames (symbol . last) "."

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

-- Insert measure info for every constructor
-- that appears in the expression e
-- required by PMEquivalence.mconcatChunk
assertSelectors :: Knowledge -> Expr -> EvalST ()
assertSelectors _ _ = return ()
-- ADT/DATACONS TAKES CARE OF THIS
-- assertSelectors γ e = do
   -- EvalEnv _ _ evaenv <- get
   -- let sims = aenvSimpl evaenv
   -- _ <- foldlM (\_ s -> Vis.mapMExpr (go s) e) e sims
   -- return ()
  -- where
    -- go :: Rewrite -> Expr -> EvalST Expr
    -- go (SMeasure f dc xs bd) e@(EApp _ _)
      -- | (EVar dc', es) <- splitEApp e
      -- , dc == dc', length xs == length es
      -- = addSMTEquality γ (EApp (EVar f) e) (subst (mkSubst $ zip xs es) bd)
      -- >> return e
    -- go _ e
      -- = return e

-- addSMTEquality :: Knowledge -> Expr -> Expr -> EvalST (IO ())
-- addSMTEquality γ e1 e2 =
--  return $ do ctx <- knContext γ
--              SMT.smtAssert ctx (PAtom Eq (makeLam γ e1) (makeLam γ e2))

--------------------------------------------------------------------------------
-- | Symbolic Evaluation with SMT
--------------------------------------------------------------------------------
data EvalEnv = EvalEnv { evId        :: Int
                       , evSequence  :: [(Expr,Expr)]
                       , _evAEnv     :: AxiomEnv
                       }

type EvalST a = StateT EvalEnv IO a

evaluate :: Config -> SMT.Context -> [(Symbol, SortedReft)] -> AxiomEnv
            -> [Expr]
            -> IO [(Expr, Expr)]
evaluate cfg ctx facts aenv einit
  = (eqs ++) <$>
    (fmap join . sequence)
    (evalOne <$> L.nub (grepTopApps =<< einit))
  where
    (eqs, γ) = makeKnowledge cfg ctx aenv facts
    initEvalSt = EvalEnv 0 [] aenv
    -- This adds all intermediate unfoldings into the assumptions
    -- no test needs it
    -- TODO: add a flag to enable it
    evalOne :: Expr -> IO [(Expr, Expr)]
    evalOne e = do
      (e', st) <- runStateT (eval γ e) initEvalSt
      if e' == e then return [] else return ((e, e'):evSequence st)

-- Don't evaluate under Lam, App, Ite, or constants
grepTopApps :: Expr -> [Expr]
grepTopApps (PAnd es)       = concatMap grepTopApps es
grepTopApps (POr es)        = concatMap grepTopApps es
grepTopApps (PAtom _ e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps (PIff e1 e2)    = grepTopApps e1 ++ grepTopApps e2
grepTopApps (PImp e1 e2)    = grepTopApps e1 ++ grepTopApps e2
grepTopApps (PNot e)        = grepTopApps e
grepTopApps (EBin  _ e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps (ENeg e)        = grepTopApps e
grepTopApps e@(EApp _ _)    = [e]
grepTopApps _               = []

-- AT: I think makeLam is the adjoint of splitEApp?
makeLam :: Knowledge -> Expr -> Expr
makeLam γ e = foldl (flip ELam) e (knLams γ)

eval :: Knowledge -> Expr -> EvalST Expr
eval γ e | Just e' <- lookupKnowledge γ e
  = (e, "Knowledge") ~> e'
eval γ (ELam (x,s) e)
  -- SHIFTLAM (assuming this shifting is redundant if DEFUNC has already happened)
  -- = do let x' = lamArgSymbol (1 + length (knLams γ))
       -- e'    <- eval γ{knLams = (x',s):knLams γ} (subst1 e (x, EVar x'))
       -- return $ ELam (x,s) $ subst1 e' (x', EVar x)

  = do e'    <- eval γ{knLams = (x, s) : knLams γ} e
       return $ ELam (x, s) e'

eval γ e@(EIte b e1 e2)
  = do b' <- eval γ b
       evalIte γ e b' e1 e2
eval γ e@(EApp _ _)
  = evalArgs γ e >>= evalApp γ e
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
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc))
                        (knSims γ)
  , length (smArgs simp) == length es
  = do e'    <- eval γ $ η $ substPopIf (zip (smArgs simp) es) (smBody simp)
       (e, "Rewrite -" ++ showpp f) ~> e'
evalApp γ _ (EVar f, es)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es
  , f `notElem` syms bd -- not recursive
  = eval γ $ η $ substPopIf (zip (eqArgs eq) es) bd
evalApp γ _e (EVar f, es)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es  --  recursive
  = evalRecApplication γ (eApps (EVar f) es) $
    subst (mkSubst $ zip (eqArgs eq) es) bd
evalApp _ _ (f, es)
  = return $ eApps f es

substPopIf :: [(Symbol, Expr)] -> Expr -> Expr
substPopIf xes e = η $ foldl go e xes
  where
    go e (x, EIte b e1 e2) = EIte b (subst1 e (x, e1)) (subst1 e (x, e2))
    go e (x, ex)           = subst1 e (x, ex)

evalRecApplication :: Knowledge -> Expr -> Expr -> EvalST Expr
evalRecApplication γ e (EIte b e1 e2)
  = do b' <- eval γ b
       b'' <- liftIO (isValid γ b')
       if b''
          then addApplicationEq γ e e1 >>
               ({-# SCC "assertSelectors-1" #-} assertSelectors γ e1) >>
               eval γ e1 >>=
               ((e, "App") ~>)
          else do b''' <- liftIO (isValid γ (PNot b'))
                  if b'''
                     then addApplicationEq γ e e2 >>
                          ({-# SCC "assertSelectors-1" #-} assertSelectors γ e2) >>
                          eval γ e2 >>=
                          ((e, "App") ~>)
                     else return e
evalRecApplication _ _ e
  = return e

addApplicationEq :: Knowledge -> Expr -> Expr -> EvalST ()
addApplicationEq γ e1 e2 =
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

-- normalization required by ApplicativeMaybe.composition
---------------------------------------------------------
η :: Expr -> Expr
η = snd . go
  where
    go (EIte b t f)
      | isTautoPred t && isFalse f
      = (True, b)
    go (EIte b e1 e2)
      = let (fb, b') = go b
            (f1, e1') = go e1
            (f2, e2') = go e2
            in
        (fb || f1 || f2, EIte b' e1' e2')
    go (EApp (EIte b f1 f2) e)
      = (True, EIte b (snd $ go $ EApp f1 e) (snd $ go $ EApp f2 e))
    go (EApp f (EIte b e1 e2))
      = (True, EIte b (snd $ go $ EApp f e1) (snd $ go $ EApp f e2))
    go (EApp e1 e2)
      = let (f1, e1') = go e1
            (f2, e2') = go e2
            in
        if f1 || f2
              then go $ EApp e1' e2'
              else (False, EApp e1' e2')
    go e = (False, e)

instance Expression (Symbol, SortedReft) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)
