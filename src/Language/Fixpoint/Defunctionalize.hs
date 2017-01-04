{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE OverloadedStrings    #-}

--------------------------------------------------------------------------------
-- | `defunctionalize` traverses the query to:
--      1. "normalize" lambda terms by renaming binders,
--      2. generate alpha- and beta-equality axioms for
--   The lambdas and redexes found in the query.
--
--   NOTE: `defunctionalize` should happen **BEFORE**
--   `elaborate` as the latter converts all actual `EApp`
--   into the (uninterpreted) `smt_apply`.
--   We cannot elaborate prior to `defunc` as we need the
--   `EApp` and `ELam` to determine the lambdas and redexes.
--------------------------------------------------------------------------------

module Language.Fixpoint.Defunctionalize (defunctionalize) where

import qualified Data.HashMap.Strict as M
import           Data.Hashable
import           Data.Maybe             (maybeToList)
import qualified Data.List           as L

import           Control.Monad.State
import           Language.Fixpoint.Misc            (sortNub, fM, whenM, secondM, mapSnd)
import           Language.Fixpoint.Solver.Sanitize (symbolEnv)
import           Language.Fixpoint.Types        hiding (allowHO)
import           Language.Fixpoint.Types.Config
-- NOPROP import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types.Visitor   (mapMExpr, stripCasts)


defunctionalize :: (Fixpoint a) => Config -> SInfo a -> SInfo a
defunctionalize cfg si = evalState (defunc si) (makeInitDFState cfg si)

--------------------------------------------------------------------------------
-- | Expressions defunctionalization -------------------------------------------
--------------------------------------------------------------------------------
txExpr :: Expr -> DF Expr
txExpr e = do
  hoFlag <- gets dfHO
  if hoFlag then defuncExpr e else return e

-- NOPROP txExpr' :: Bool -> Expr -> DF Expr
-- NOPROP txExpr' hoFlag e
  -- NOPROP = defuncExpr (txExtensionality e)
  -- NOPROP | hoFlag
  -- NOPROP = defuncExpr e
  -- NOPROP | otherwise
  -- NOPROP = return e

defuncExpr :: Expr -> DF Expr
defuncExpr = mapMExpr reBind
         >=> mapMExpr logLam
         >=> mapMExpr logRedex
         >=> mapMExpr (fM normalizeLams)

reBind :: Expr -> DF Expr
reBind (ELam (x, s) e) = (\y -> ELam (y, s) (subst1 e (x, EVar y))) <$> freshSym s
reBind e               = return e

maxLamArg :: Int
maxLamArg = 7

-- NIKI TODO: allow non integer lambda arguments
-- sorts = [setSort intSort, bitVecSort intSort, mapSort intSort intSort, boolSort, realSort, intSort]
makeLamArg :: Sort -> Int  -> Symbol
makeLamArg _ = intArgName

--------------------------------------------------------------------------------

makeAxioms :: DF [Expr]
makeAxioms = do
  alphEqs <- concatMap makeAlphaAxioms <$> getLams
  betaEqs <- concatMap makeBetaAxioms  <$> getRedexes
  return   $ alphEqs ++ betaEqs

--------------------------------------------------------------------------------
-- | Alpha Equivalence ---------------------------------------------------------
--------------------------------------------------------------------------------
makeAlphaAxioms ::  Expr -> [Expr]
makeAlphaAxioms = makeAlphaEq . normalizeLams

makeAlphaEq :: Expr -> [Expr]
makeAlphaEq e = go e ++ go' e
  where
    go ee
      = makeEqForAll ee (normalize ee)
    go' ee@(ELam (x, s) e)
      = [makeEq ee ee'
         | (i, ee') <- map (\j -> normalizeLamsFromTo j (ELam (x, s) e)) [1..maxLamArg-1]
         , i <= maxLamArg ]
    go' _
      = []

--------------------------------------------------------------------------------
-- | Normalizations ------------------------------------------------------------
--------------------------------------------------------------------------------

-- head normal form [TODO: example]

normalize :: Expr -> Expr
normalize = snd . go
  where
    go (ELam (y, sy) e) = let (i', e') = go e
                              y'      = makeLamArg sy i'
                          in (i'+1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e e2)
      |  (ELam (x, _) bd) <- unECst e
                        = let (i1, e1') = go bd
                              (i2, e2') = go e2
                          in (max i1 i2, e1' `subst1` (x, e2'))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go (PAll bs e)      = mapSnd (PAll bs)  (go e)
    go e                = (1, e)

    unECst (ECst e _) = unECst e
    unECst e          = e

-- normalize lambda arguments [TODO: example]

normalizeLams :: Expr -> Expr
normalizeLams e = snd $ normalizeLamsFromTo 1 e

normalizeLamsFromTo :: Int -> Expr -> (Int, Expr)
normalizeLamsFromTo i   = go
  where
    go (ELam (y, sy) e) = let (i', e') = go e
                              y'      = makeLamArg sy i'
                          in (i' + 1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go (PAll bs e)      = mapSnd (PAll bs) (go e)
    go e                = (i, e)

--------------------------------------------------------------------------------
-- | Beta Equivalence ----------------------------------------------------------
--------------------------------------------------------------------------------
makeBetaAxioms :: Expr -> [Expr]
makeBetaAxioms e = makeEqForAll (tracepp ("BETA-NL e = " ++ showpp e) $ normalizeLams e) (normalize e)

makeEq :: Expr -> Expr -> Expr
makeEq e1 e2
  | e1 == e2  = PTrue
  | otherwise = EEq e1 e2

makeEqForAll :: Expr -> Expr -> [Expr]
makeEqForAll e1 e2 =
  [ makeEq (closeLam su e1') (closeLam su e2') | su <- instantiate xs]
  where
    (xs1, e1') = splitPAll [] e1
    (xs2, e2') = splitPAll [] e2
    xs         = L.nub (xs1 ++ xs2)

closeLam :: [(Symbol, (Symbol, Sort))] -> Expr -> Expr
closeLam ((x,(y,s)):su) e = ELam (y,s) (subst1 (closeLam su e) (x, EVar y))
closeLam []             e = e

splitPAll :: [(Symbol, Sort)] -> Expr -> ([(Symbol, Sort)], Expr)
splitPAll acc (PAll xs e) = splitPAll (acc ++ xs) e
splitPAll acc e           = (acc, e)

instantiate :: [(Symbol, Sort)] -> [[(Symbol, (Symbol,Sort))]]
instantiate []     = [[]]
instantiate xs     = L.foldl' (\acc x -> combine (instOne x) acc) [] xs
  where
    instOne (x, s) = [(x, (makeLamArg s i, s)) | i <- [1..maxLamArg]]
    combine xs []  = [[x] | x <- xs]
    combine xs acc = concat [(x:) <$> acc | x <- xs]

-- NOPROP
-- NOPROP --------------------------------------------------------------------------------
-- NOPROP -- | Extensionality ------------------------------------------------------------
-- NOPROP --------------------------------------------------------------------------------
-- NOPROP
-- NOPROP txExtensionality :: Expr -> Expr
-- NOPROP txExtensionality = mapExpr' go
  -- NOPROP where
    -- NOPROP go (EEq e1 e2)
      -- NOPROP | FFunc _ _ <- exprSort "txn5" e1
      -- NOPROP , FFunc _ _ <- exprSort "txn6" e2
      -- NOPROP = mkExFunEq e1 e2
    -- NOPROP go e
      -- NOPROP = e
-- NOPROP
-- NOPROP mkExFunEq :: Expr -> Expr -> Expr
-- NOPROP mkExFunEq e1 e2 = PAnd [PAll (zip xs ss)
                             -- NOPROP (EEq
                                -- NOPROP (ECst (eApps e1' es) s)
                                -- NOPROP (ECst (eApps e2' es) s))
                       -- NOPROP , EEq e1 e2]
  -- NOPROP where
    -- NOPROP es      = zipWith (\x s -> ECst (EVar x) s) xs ss
    -- NOPROP xs      = (\i -> symbol ("local_fun_arg" ++ show i)) <$> [1..length ss]
    -- NOPROP (s, ss) = splitFun [] s1
    -- NOPROP s1      = exprSort "txn7" e1
-- NOPROP
    -- NOPROP splitFun acc (FFunc s ss) = splitFun (s:acc) ss
    -- NOPROP splitFun acc s            = (s, reverse acc)
-- NOPROP
    -- NOPROP e1' = ECst e1 s1
    -- NOPROP e2' = ECst e2 s1
-- NOPROP
-- NOPROP -- RJ: according to https://github.com/ucsd-progsys/liquid-fixpoint/commit/d8b742b29c8a892fc947eb90fe6eb949207f65cb
-- NOPROP -- the `Visitor.mapExpr` "diverges".
-- NOPROP -- This is because the mapper works in a "top-down" fashion, i.e. it first
-- NOPROP -- converts `e` into `e /\ e1` and then recursively traverses `e` which means
-- NOPROP -- it spins forever.
-- NOPROP
-- NOPROP mapExpr' :: (Expr -> Expr) -> Expr -> Expr
-- NOPROP mapExpr' f = go
  -- NOPROP where
    -- NOPROP go (ELam bs e)     = f (ELam bs (go e))
    -- NOPROP go (ECst e s)      = f (ECst (go e) s)
    -- NOPROP go (EApp e1 e2)    = f (EApp (go e1) (go e2))
    -- NOPROP go e@(ESym _)      = f e
    -- NOPROP go e@(ECon _)      = f e
    -- NOPROP go e@(EVar _)      = f e
    -- NOPROP go (ENeg e)        = f $ ENeg (go e)
    -- NOPROP go (EBin b e1 e2)  = f $ EBin b (go e1) (go e2)
    -- NOPROP go (EIte e e1 e2)  = f $ EIte (go e) (go e1) (go e2)
    -- NOPROP go (ETAbs e t)     = f $ ETAbs (go e) t
    -- NOPROP go (ETApp e t)     = f $ ETApp (go e) t
    -- NOPROP go (PAnd es)       = f $ PAnd $ map go es
    -- NOPROP go (POr es)        = f $ POr  $ map go es
    -- NOPROP go (PNot e)        = f $ PNot $ go e
    -- NOPROP go (PImp e1 e2)    = f $ PImp (go e1) (go e2)
    -- NOPROP go (PIff e1 e2)    = f $ PIff (go e1) (go e2)
    -- NOPROP go (PAtom a e1 e2) = f $ PAtom a (go e1) (go e2)
    -- NOPROP go (PAll bs e)     = f $ PAll bs   $  go e
    -- NOPROP go (PExist bs e)   = f $ PExist bs $ go e
    -- NOPROP go e@(PKVar _ _ )  = f e
    -- NOPROP go e@PGrad         = f e

--------------------------------------------------------------------------------
-- | Containers defunctionalization --------------------------------------------
--------------------------------------------------------------------------------

class Defunc a where
  defunc :: a -> DF a

instance (Defunc (c a), TaggedC c a) => Defunc (GInfo c a) where
  defunc fi = do
    cm'    <- defunc $ cm    fi
    ws'    <- defunc $ ws    fi
    -- NOPROP setBinds $ mconcat ((senv <$> M.elems (cm fi)) ++ (wenv <$> M.elems (ws fi)))
    gLits' <- defunc $ gLits fi
    dLits' <- defunc $ dLits fi
    bs'    <- defunc $ bs    fi
    -- NOPROP quals' <- defunc $ quals fi
    axioms <- makeAxioms
    return $ fi { cm      = cm'
                , ws      = ws'
                , gLits   = gLits'
                , dLits   = dLits'
                , bs      = bs'
                -- NOPROP , quals   = quals'
                , asserts = axioms
                }

instance Defunc (SimpC a) where
  defunc sc = do crhs' <- defunc $ _crhs sc
                 return $ sc {_crhs = crhs'}

instance Defunc (WfC a)   where
  defunc wf = do
    let (x, t, k) = wrft wf
    t' <- defunc t
    return $ wf { wrft = (x, t', k) }

instance Defunc SortedReft where
  defunc (RR s r) = RR s <$> defunc r

instance Defunc (Symbol, SortedReft) where
  defunc (x, sr) = (x,) <$> defunc sr

instance Defunc (Symbol, Sort) where
  defunc (x, t) = (x,) <$> defunc t

instance Defunc Reft where
  defunc (Reft (x, e)) = Reft . (x,) <$> defunc e

instance Defunc Expr where
  defunc = txExpr

instance Defunc a => Defunc (SEnv a) where
  defunc = mapMSEnv defunc

instance Defunc BindEnv   where
  defunc bs = do dfbs <- gets dfBEnv
                 let f (i, xs) = if i `memberIBindEnv` dfbs
                                       then  (i,) <$> defunc xs
                                       else  (i,) <$> matchSort xs
                 mapWithKeyMBindEnv f bs
   where
    -- The refinement cannot be elaborated thus defunc-ed because
    -- the bind does not appear in any contraint,
    -- thus unique binders does not perform properly
    -- The sort should be defunc, to ensure same sort on double binders
    matchSort (x, RR s r) = ((x,) . (`RR` r)) <$> defunc s

-- Sort defunctionalization [should be done by elaboration]
instance Defunc Sort where
  defunc = return

instance Defunc a => Defunc [a] where
  defunc = mapM defunc

instance (Defunc a, Eq k, Hashable k) => Defunc (M.HashMap k a) where
  defunc m = M.fromList <$> mapM (secondM defunc) (M.toList m)

type DF    = State DFST

data DFST = DFST
  { dfFresh   :: !Int
  , dfEnv   :: !(SEnv Sort)
  , dfBEnv  :: !IBindEnv
  , dfLam   :: !Bool        -- ^ normalize lams
  , dfExt   :: !Bool        -- ^ enable extensionality axioms
  , dfAEq   :: !Bool        -- ^ enable alpha equivalence axioms
  , dfBEq   :: !Bool        -- ^ enable beta equivalence axioms
  , dfNorm  :: !Bool        -- ^ enable normal form axioms
  , dfHO    :: !Bool        -- ^ allow higher order thus defunctionalize
  , dfLNorm :: !Bool
  , dfLams  :: ![Expr]      -- ^ lambda expressions appearing in the expressions
  , dfRedex :: ![Expr]      -- ^ redexes appearing in the expressions
  , dfBinds :: !(SEnv Sort) -- ^ sorts of new lambda-binders
  }

makeInitDFState :: Config -> SInfo a -> DFST
makeInitDFState cfg si = DFST
  { dfFresh = 0
  , dfEnv   = symbolEnv cfg si -- NOPROP fromListSEnv xs
  , dfBEnv  = mconcat ((senv <$> M.elems (cm si)) ++ (wenv <$> M.elems (ws si)))
  , dfLam   = True
  , dfExt   = False -- extensionality   cfg
  , dfAEq   = alphaEquivalence cfg
  , dfBEq   = betaEquivalence  cfg
  , dfNorm  = normalForm       cfg
  , dfHO    = allowHO cfg  || defunction cfg
  , dfLNorm = True
  -- INVARIANT: lambads and redexes are not defunctionalized
  , dfLams  = []
  , dfRedex = []
  , dfBinds = mempty
  }

--------------------------------------------------------------------------------
-- | Low level monad manipulation ----------------------------------------------
--------------------------------------------------------------------------------
freshSym :: Sort -> DF Symbol
freshSym t = do
  n    <- gets dfFresh
  let x = intSymbol "lambda_fun_" n
  modify $ \s -> s {dfFresh = n + 1, dfBinds = insertSEnv x t (dfBinds s)}
  return x

logLam :: Expr -> DF Expr
logLam e = whenM (gets dfAEq) (putLam e) >> return e

logRedex :: Expr -> DF Expr
logRedex e = whenM (gets dfBEq) (putRedex e) >> return e

putLam :: Expr -> DF ()
putLam e@(ELam {}) = modify $ \s -> s { dfLams = e : dfLams s}
putLam _           = return ()

putRedex :: Expr -> DF ()
putRedex e@(EApp f _)
  | ELam _ _ <- stripCasts f
  = modify $ \s -> s { dfRedex = e : dfRedex s }
putRedex _
  = return ()


-- | getLams and getRedexes return the (previously seen) lambdas and redexes,
--   after "closing" them by quantifying out free vars corresponding to the
--   fresh binders in `dfBinds`.
getLams    :: DF [Expr]
getLams    = getClosedField dfLams

getRedexes :: DF [Expr]
getRedexes = getClosedField dfRedex

getClosedField :: (DFST -> [Expr]) -> DF [Expr]
getClosedField fld = do
  env <- gets dfBinds
  es  <- gets fld
  return (closeLams env <$> es)

closeLams :: SEnv Sort -> Expr -> Expr
closeLams env e = PAll (freeBinds env e) e

freeBinds :: SEnv Sort -> Expr -> [(Symbol, Sort)]
freeBinds env e = [ (y, t) | y <- sortNub (syms e)
                           , t <- maybeToList (lookupSEnv y env) ]
