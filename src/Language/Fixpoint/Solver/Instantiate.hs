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
import           Language.Fixpoint.Types.Config as FC
import           Language.Fixpoint.Types.Visitor (eapps, kvars, mapMExpr)
import           Language.Fixpoint.Misc          (mapFst)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize (defuncAny, makeLamArg)
import           Language.Fixpoint.SortCheck       (applySorts, elaborate)
import           Control.Monad.State

-- AT: I've inlined this, but we should have a more elegant solution
--     (track predicates instead of selectors!)
-- import           Language.Haskell.Liquid.GHC.Misc (dropModuleNames)
import qualified Data.Text            as T
import qualified Data.HashMap.Strict  as M
import qualified Data.List            as L
import           Data.Maybe           (catMaybes, fromMaybe)
import           Data.Char            (isUpper)
import           Data.Foldable        (foldlM)

(~>) :: (Expr, String) -> Expr -> EvalST Expr
(_e,_str) ~> e' = do
    modify (\st -> st{evId = evId st + 1})
    -- traceM $ showpp _str ++ " : " ++ showpp _e ++ showpp e'
    return (η e')


-------------------------------------------------------------------------------
-- | Instantiate Axioms
-------------------------------------------------------------------------------
instantiate :: Config -> FInfo c -> IO (FInfo c)
instantiate cfg fi = do
    -- ctx <- SMT.makeContextWithSEnv cfg file env
    ctx <- SMT.makeSmtContext cfg file (ddecls fi) []
            (tracepp "APPLY-SORTS" $ applySorts fi) -- _fixme_need_apply_sorts_here
    SMT.smtPush ctx
    cm' <- sequence $ M.mapWithKey (inst1 ctx) (cm fi)
    return $ fi { cm = cm' }
  where
    file      = srcFile cfg ++ ".evals"
    -- env       = symEnv mempty (Thy.theorySymbols fi) -- _symbolEnv cfg fi
    inst1 ctx = instAxioms cfg ctx (bs fi) (gLits fi) (ae fi)

instAxioms :: Config -> SMT.Context -> BindEnv -> SEnv Sort -> AxiomEnv
                  -> Integer -> SubC c
                  -> IO (SubC c)
instAxioms _ _ _ _ aenv sid sub
  | not (M.lookupDefault False sid (aenvExpand aenv))
  = return sub
instAxioms cfg ctx bds fenv aenv sid sub
  = flip strengthenLhs sub . pAnd . (is0 ++) .
    (if arithmeticAxioms cfg then (is ++) else id) <$>
    if rewriteAxioms cfg then evalEqs else return []
  where
    is0              = eqBody <$> L.filter (null . eqArgs) eqs
    is               = instances maxNumber aenv initOccurences
    evalEqs          =
       map (uncurry (PAtom Eq)) .
       filter (uncurry (/=)) <$>
       evaluate cfg ctx ((vv Nothing, slhs sub):binds) fenv aenv initExpressions
    initExpressions  = expr (slhs sub) : expr (srhs sub) : (expr <$> binds)
    binds            = envCs bds (senv sub)
    initOccurences   = concatMap (makeInitOccurences as eqs) initExpressions

    eqs = aenvEqs aenv

    -- fuel calculated and used only by `instances` arith rewrite method
    fuelNumber = M.lookupDefault 0 sid (aenvFuel aenv)
    as         = (,fuelNumber) . eqName <$> filter (not . null . eqArgs) eqs
    maxNumber  = (aenvSyms aenv * length initOccurences) ^ fuelNumber

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
emptyKnowledge cxt = KN [] [] [] [] cxt (\_ _ _ -> return False) []

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

makeKnowledge :: Config -> SMT.Context -> AxiomEnv -> SEnv Sort
                 -> [(Symbol, SortedReft)]
                 -> ([(Expr, Expr)], Knowledge)
makeKnowledge cfg ctx aenv fenv es = (simpleEqs,) $ (emptyKnowledge context)
                                     { knSels   = sels
                                     , knEqs    = eqs
                                     , knSims   = aenvSimpl aenv
                                     , knAms    = aenvEqs aenv
                                     , knPreds  = \bs e c -> askSMT c bs e
                                     }
  where
    (xv, sv) = (vv Nothing, sr_sort $ snd $ head es)
    fbinds   = toListSEnv fenv ++ [(x, s) | (x, RR s _) <- es]
    senv     = senvCtx { seSort = fromListSEnv fbinds }
    thySyms  = seTheory senvCtx
    senvCtx  = SMT.ctxSymEnv ctx
    context :: IO SMT.Context
    context = do
      SMT.smtPop ctx
      SMT.smtPush ctx
      SMT.smtDecls ctx $ L.nub [(x, toSMT [] s) | (x, s) <- fbinds, not (memberSEnv x thySyms)]
      SMT.smtAssert ctx (pAnd ([toSMT [] (PAtom Eq e1 e2) | (e1, e2) <- simpleEqs]
                               ++ filter (null.kvars) ((toSMT [] . expr) <$> es)
                              ))
      return ctx

    -- This creates the rewrite rule e1 -> e2
    -- when should I apply it?
    -- 1. when e2 is a data con and can lead to further reductions
    -- 2. when size e2 < size e1
    -- @TODO: Can this be generalized?
    atms = splitPAnd =<< (expr <$> filter isProof es)
    simpleEqs = makeSimplifications (aenvSimpl aenv) =<<
                L.nub (catMaybes [getDCEquality e1 e2 | PAtom Eq e1 e2 <- atms])
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

    toSMT xs = defuncAny cfg senv0
             . elaborate "symbolic evaluation" (elabEnv xs)
    elabEnv  = L.foldl' (\env (x, s) -> insertSymEnv x s env) senv0
    senv0    = insertSymEnv xv sv senv

    -- AT: Non-obvious needed invariant: askSMT True is always the
    -- totality-effecting one
    askSMT :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
    askSMT cxt xss e
      | isTautoPred  e = return True
      | isContraPred e = return False
      | null (kvars e) = do
          SMT.smtPush cxt
          b <- SMT.checkValid' cxt [] PTrue (toSMT xss e)
          SMT.smtPop cxt
          return b
      | otherwise      = return False

    -- TODO: Stringy hacks
    isSelector :: Symbol -> Bool
    isSelector  = L.isPrefixOf "select" . symbolString
    isProof (_, RR s _) =  showpp s == "Tuple"

makeSimplifications :: [Rewrite] -> (Symbol, [Expr], Expr) -> [(Expr, Expr)]
makeSimplifications sis (dc, es, e)
 = go =<< sis
 where
   go (SMeasure f dc' xs bd)
     | dc == dc', length xs == length es
     = [(EApp (EVar f) e, subst (mkSubst $ zip xs es) bd)]
   go _
     = []

getDCEquality :: Expr -> Expr -> Maybe (Symbol, [Expr], Expr)
getDCEquality e1 e2
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
    (f1, es1) = mapFst getDC $ splitEApp e1
    (f2, es2) = mapFst getDC $ splitEApp e2

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
assertSelectors γ e = do
   EvalEnv _ _ evaenv <- get
   let sims = aenvSimpl evaenv
   _ <- foldlM (\_ s -> mapMExpr (go s) e) e sims
   return ()
  where
    go :: Rewrite -> Expr -> EvalST Expr
    go (SMeasure f dc xs bd) e@(EApp _ _)
      | (EVar dc', es) <- splitEApp e
      , dc == dc', length xs == length es
      = addSMTEquality γ (EApp (EVar f) e) (subst (mkSubst $ zip xs es) bd)
      >> return e
    go _ e
      = return e

addSMTEquality :: Knowledge -> Expr -> Expr -> EvalST (IO ())
addSMTEquality γ e1 e2 =
  return $ do ctx <- knContext γ
              SMT.smtAssert ctx (PAtom Eq (makeLam γ e1) (makeLam γ e2))

--------------------------------------------------------------------------------
-- | Symbolic Evaluation with SMT
--------------------------------------------------------------------------------
data EvalEnv = EvalEnv { evId        :: Int
                       , evSequence  :: [(Expr,Expr)]
                       , _evAEnv     :: AxiomEnv
                       }

type EvalST a = StateT EvalEnv IO a

evaluate :: Config -> SMT.Context -> [(Symbol, SortedReft)] -> SEnv Sort -> AxiomEnv
            -> [Expr]
            -> IO [(Expr, Expr)]
evaluate cfg ctx facts fenv aenv einit
  = (eqs ++) <$>
    (fmap join . sequence)
    (evalOne <$> L.nub (grepTopApps =<< einit))
  where
    (eqs, γ) = makeKnowledge cfg ctx aenv fenv facts
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
grepTopApps (PAnd es) = concatMap grepTopApps es
grepTopApps (POr es) = concatMap grepTopApps es
grepTopApps (PAtom _ e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps (PIff e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps (PImp e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps (PNot e) = grepTopApps e
grepTopApps (EBin  _ e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps (ENeg e) = grepTopApps e
grepTopApps e@(EApp _ _) = [e]
grepTopApps _ = []

-- AT: I think makeLam is the adjoint of splitEApp?
makeLam :: Knowledge -> Expr -> Expr
makeLam γ e = foldl (flip ELam) e (knLams γ)

eval :: Knowledge -> Expr -> EvalST Expr
eval γ e | Just e' <- lookupKnowledge γ e
   = (e, "Knowledge") ~> e'
eval γ (ELam (x,s) e)
  = do let x' = makeLamArg s (1+ length (knLams γ))
       e'    <- eval γ{knLams = (x',s):knLams γ} (subst1 e (x, EVar x'))
       return $ ELam (x,s) $ subst1 e' (x', EVar x)
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
eval _ e = return e

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

evalRecApplication :: Knowledge ->  Expr -> Expr -> EvalST Expr
evalRecApplication γ e (EIte b e1 e2)
  = do b' <- eval γ b
       b'' <- liftIO (isValid γ b')
       if b''
          then addApplicationEq γ e e1 >>
               assertSelectors γ e1 >>
               eval γ e1 >>=
               ((e, "App") ~>)
          else do b''' <- liftIO (isValid γ (PNot b'))
                  if b'''
                     then addApplicationEq γ e e2 >>
                          assertSelectors γ e2 >>
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


-- Fuel
-------
type Fuel = Int
type FuelMap = [(Symbol, Fuel)]

goodFuelMap :: FuelMap -> Bool
goodFuelMap = any ((>0) . snd)

hasFuel :: FuelMap -> Symbol -> Bool
hasFuel fm x = maybe True (\x -> 0 < x) (L.lookup x fm)

makeFuelMap :: (Fuel -> Fuel) -> FuelMap -> Symbol -> FuelMap
makeFuelMap f ((x, fx):fs) y
  | x == y    = (x, f fx) : fs
  | otherwise = (x, fx)   : makeFuelMap f fs y
makeFuelMap _ _ _ = error "makeFuelMap"

----------------------------
-- Naive evaluation strategy
----------------------------
data Occurence = Occ {_ofun :: Symbol, _oargs :: [Expr], ofuel :: FuelMap}
 deriving (Show)

instances :: Int -> AxiomEnv -> [Occurence] -> [Expr]
instances maxIs aenv !occs
  = instancesLoop aenv maxIs eqs occs -- (eqBody <$> eqsZero) ++ is
  where
    eqs = filter (not . null . eqArgs) (aenvEqs  aenv)

-- Naively: Instantiation happens arbitrary times (in recursive functions it
-- diverges)
-- Step 1 [done] : Hack it so that instantiation of axiom A happens from an
-- occurences and its subsequent instances <= FUEL times
-- How? Hack expressions to contatin fuel info within eg Cst Step 2: Compute
-- fuel based on Ranjit's algorithm

instancesLoop :: AxiomEnv ->  Int -> [Equation] -> [Occurence] -> [Expr]
instancesLoop _ _ eqs = go 0 []
  where
    go :: Int -> [Expr] -> [Occurence] -> [Expr]
    go !i acc occs
       = let is      = concatMap (unfold eqs) occs
             newIs   = findNewEqs is acc
             newOccs = concatMap (grepOccurences eqs) newIs
             in
         if null newIs
            then acc
            else go (i + length newIs) ((fst <$> newIs) ++ acc) newOccs

findNewEqs :: [(Expr, FuelMap)] -> [Expr] -> [(Expr, FuelMap)]
findNewEqs [] _ = []
findNewEqs ((e, f):xss) es
  | e `elem` es = findNewEqs xss es
  | otherwise   = (e,f):findNewEqs xss es

makeInitOccurences :: [(Symbol, Fuel)] -> [Equation] -> Expr -> [Occurence]
makeInitOccurences xs eqs e
  = [Occ x es xs | (EVar x, es) <- splitEApp <$> eapps e
                 , Equ x' xs' _ <- eqs, x == x'
                 , length xs' == length es]

grepOccurences :: [Equation] -> (Expr, FuelMap) -> [Occurence]
grepOccurences eqs (e, fs)
  = filter (goodFuelMap . ofuel)
           [Occ x es fs | (EVar x, es) <- splitEApp <$> eapps e
                        , Equ x' xs' _ <- eqs, x == x'
                        , length xs' == length es]

unfold :: [Equation] -> Occurence -> [(Expr, FuelMap)]
unfold eqs (Occ x es fs)
  = catMaybes [if hasFuel fs x
                  then Just (subst (mkSubst $ zip  xs' es) e
                            , makeFuelMap (\x -> x-1) fs x)
                  else Nothing
              | Equ x' xs' e <- eqs
              , x == x'
              , length xs' == length es]

instance Expression (Symbol, SortedReft) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)
