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

module Language.Fixpoint.Defunctionalize 
  ( defunctionalize
  , Defunc(..)
  , defuncAny
  , defuncAxioms
  ) where 

import qualified Data.HashMap.Strict as M
import           Data.Hashable
import qualified Data.List           as L
import           Control.Monad.State
import           Language.Fixpoint.Misc            (fM, secondM, mapSnd)
import           Language.Fixpoint.Solver.Sanitize (symbolEnv)
import           Language.Fixpoint.Types        hiding (allowHO)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Visitor   (mapMExpr)
-- import Debug.Trace (trace)

defunctionalize :: (Fixpoint a) => Config -> SInfo a -> SInfo a
defunctionalize cfg si = evalState (defunc si) (makeInitDFState cfg si)

defuncAny :: Defunc a => Config -> SymEnv -> a -> a
defuncAny cfg env e = evalState (defunc e) (makeDFState cfg env emptyIBindEnv)

defuncAxioms :: (Defunc a) => Config -> SymEnv -> a -> (a, [Triggered Expr])
defuncAxioms cfg env z = flip evalState (makeDFState cfg env emptyIBindEnv) $ do
  z' <- defunc z
  return (z', [])

---------------------------------------------------------------------------------------------
-- | Expressions defunctionalization --------------------------------------------------------
---------------------------------------------------------------------------------------------
txExpr :: Expr -> DF Expr
txExpr e = do
  hoFlag <- gets dfHO
  if hoFlag then defuncExpr e else return e

defuncExpr :: Expr -> DF Expr
defuncExpr = mapMExpr reBind
         >=> mapMExpr (fM normalizeLams)

reBind :: Expr -> DF Expr
reBind (ELam (x, s) e) = ((\y -> ELam (y, s) (subst1 e (x, EVar y))) <$> freshSym s)
reBind e               = return e

maxLamArg :: Int
maxLamArg = 7


--------------------------------------------------------------------------------
-- | Normalizations ------------------------------------------------------------
--------------------------------------------------------------------------------

-- head normal form [TODO: example]

normalize :: Expr -> Expr
normalize = snd . go
  where
    go (ELam (y, sy) e) = (i + 1, shiftLam i y sy e') where (i, e') = go e
                              -- y'       = lamArgSymbol i'  -- SHIFTLAM
                          -- in  -- ELam (y', sy) (e' `subst1` (y, EVar y')))

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

shiftLam :: Int -> Symbol -> Sort -> Expr -> Expr
shiftLam i x t e = ELam (x_i, t) (e `subst1` (x, x_i_t))
  where
    x_i          = lamArgSymbol i
    x_i_t        = ECst (EVar x_i) t

-- normalize lambda arguments [TODO: example]

normalizeLams :: Expr -> Expr
normalizeLams e = snd $ normalizeLamsFromTo 1 e

normalizeLamsFromTo :: Int -> Expr -> (Int, Expr)
normalizeLamsFromTo i   = go
  where
    go (ELam (y, sy) e) = (i + 1, shiftLam i y sy e') where (i, e') = go e
                          -- let (i', e') = go e
                          --    y'       = lamArgSymbol i'  -- SHIFTLAM
                          -- in (i' + 1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go (PAll bs e)      = mapSnd (PAll bs) (go e)
    go e                = (i, e)

--------------------------------------------------------------------------------
-- | Beta Equivalence ----------------------------------------------------------
--------------------------------------------------------------------------------
_makeBetaAxioms :: Expr -> [Expr]
_makeBetaAxioms e = makeEqForAll (normalizeLams e) (normalize e)
  -- where
  --  e             = trace ("BETA-NL e = " ++ showpp e0) e0

makeEq :: Expr -> Expr -> Expr
makeEq e1 e2
  | e1 == e2  = PTrue
  | otherwise = EEq e1 e2

makeEqForAll :: Expr -> Expr -> [Expr]
makeEqForAll e1 e2 = [ makeEq (closeLam su e1') (closeLam su e2') | su <- _instantiate xs]
  where
    (xs1, e1')     = splitPAll [] e1
    (xs2, e2')     = splitPAll [] e2
    xs             = L.nub (xs1 ++ xs2)

closeLam :: [(Symbol, (Symbol, Sort))] -> Expr -> Expr
closeLam ((x,(y,s)):su) e = ELam (y,s) (subst1 (closeLam su e) (x, EVar y))
closeLam []             e = e

splitPAll :: [(Symbol, Sort)] -> Expr -> ([(Symbol, Sort)], Expr)
splitPAll acc (PAll xs e) = splitPAll (acc ++ xs) e
splitPAll acc e           = (acc, e)

_instantiate     :: [(Symbol, Sort)] -> [[(Symbol, (Symbol, Sort))]]
_instantiate      = choices . map inst1
  where
    inst1 (x, s) = [(x, (lamArgSymbol i, s)) | i <- [1..maxLamArg]]

choices :: [[a]] -> [[a]]
choices []       = [[]]
choices (xs:xss) = [a:as | a <- xs, as <- choices xss]

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
    ass'   <- defunc $ asserts fi
    -- NOPROP quals' <- defunc $ quals fi
    return $ fi { cm      = cm'
                , ws      = ws'
                , gLits   = gLits'
                , dLits   = dLits'
                , bs      = bs'
                , asserts = ass'
                }

instance (Defunc a) => Defunc (Triggered a) where
  defunc (TR t e) = TR t <$> defunc e

instance Defunc (SimpC a) where
  defunc sc = do crhs' <- defunc $ _crhs sc
                 return $ sc {_crhs = crhs'}

instance Defunc (WfC a)   where
  defunc wf@(WfC {}) = do
    let (x, t, k) = wrft wf
    t' <- defunc t
    return $ wf { wrft = (x, t', k) }
  defunc wf@(GWfC {}) = do
    let (x, t, k) = wrft wf
    t' <- defunc t
    e' <- defunc $ wexpr wf
    return $ wf { wrft = (x, t', k), wexpr = e' }

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
  { dfFresh :: !Int
  , dfEnv   :: !SymEnv
  , dfBEnv  :: !IBindEnv
  , dfLam   :: !Bool        -- ^ normalize lams
  , dfNorm  :: !Bool        -- ^ enable normal form axioms
  , dfHO    :: !Bool        -- ^ allow higher order thus defunctionalize
  , dfLams  :: ![Expr]      -- ^ lambda expressions appearing in the expressions
  , dfRedex :: ![Expr]      -- ^ redexes appearing in the expressions
  , dfBinds :: !(SEnv Sort) -- ^ sorts of new lambda-binders
  }

makeDFState :: Config -> SymEnv -> IBindEnv -> DFST
makeDFState cfg env ibind = DFST
  { dfFresh = 0
  , dfEnv   = env
  , dfBEnv  = ibind
  , dfLam   = True
  , dfNorm  = True -- normalForm       cfg
  , dfHO    = allowHO cfg  || defunction cfg
  -- INVARIANT: lambads and redexes are not defunctionalized
  , dfLams  = []
  , dfRedex = []
  , dfBinds = mempty
  }

makeInitDFState :: Config -> SInfo a -> DFST
makeInitDFState cfg si
  = makeDFState cfg
      (symbolEnv cfg si)
      (mconcat ((senv <$> M.elems (cm si)) ++ (wenv <$> M.elems (ws si))))

--------------------------------------------------------------------------------
-- | Low level monad manipulation ----------------------------------------------
--------------------------------------------------------------------------------
freshSym :: Sort -> DF Symbol
freshSym t = do
  n    <- gets dfFresh
  let x = intSymbol "lambda_fun_" n
  modify $ \s -> s {dfFresh = n + 1, dfBinds = insertSEnv x t (dfBinds s)}
  return x


-- | getLams and getRedexes return the (previously seen) lambdas and redexes,
--   after "closing" them by quantifying out free vars corresponding to the
--   fresh binders in `dfBinds`.
