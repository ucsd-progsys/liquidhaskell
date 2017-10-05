{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}

module Language.Fixpoint.Solver.Solution
  ( -- * Create Initial Solution
    init

    -- * Update Solution
  , Sol.update

  -- * Lookup Solution
  , lhsPred
  ) where

import           Control.Parallel.Strategies
import           Control.Arrow (second)
import qualified Data.HashSet                   as S
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (fromMaybe, maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
-- import qualified Language.Fixpoint.Smt.Theories       as Thy
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types                 ((&.&))
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)
import           Language.Fixpoint.Solver.Sanitize

-- DEBUG
-- import Text.Printf (printf)
-- import           Debug.Trace (trace)


--------------------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------------------
--------------------------------------------------------------------------------
init :: (F.Fixpoint a) => Config -> F.SInfo a -> S.HashSet F.KVar -> Sol.Solution
--------------------------------------------------------------------------------
init cfg si ks = Sol.fromList senv mempty keqs [] mempty
  where
    keqs       = map (refine si qs genv) ws `using` parList rdeepseq
    qs         = F.quals si
    ws         = [ w | (k, w) <- M.toList (F.ws si), not (isGWfc w) , k `S.member` ks]
    genv       = instConstants si
    senv       = symbolEnv cfg si

--------------------------------------------------------------------------------
refine :: F.SInfo a -> [F.Qualifier] -> F.SEnv F.Sort -> F.WfC a -> (F.KVar, Sol.QBind)
refine fi qs genv w = refineK (allowHOquals fi) env qs $ F.wrft w
  where
    env             = wenv <> genv
    wenv            = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))

instConstants :: F.SInfo a -> F.SEnv F.Sort
instConstants = F.fromListSEnv . filter notLit . F.toListSEnv . F.gLits
  where
    notLit    = not . F.isLitSymbol . fst


refineK :: Bool -> F.SEnv F.Sort -> [F.Qualifier] -> (F.Symbol, F.Sort, F.KVar) -> (F.KVar, Sol.QBind)
refineK ho env qs (v, t, k) = {- F.tracepp _msg -} (k, eqs')
   where
    eqs                     = instK ho env v t qs
    eqs'                    = Sol.qbFilter (okInst env v t) eqs
    -- _msg                    = printf "\n\nrefineK: k = %s, eqs = %s" (F.showpp k) (F.showpp eqs)

--------------------------------------------------------------------------------
instK :: Bool
      -> F.SEnv F.Sort
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> Sol.QBind
--------------------------------------------------------------------------------
instK ho env v t = Sol.qb . unique . concatMap (instKQ ho env v t)
  where
    unique       = L.nubBy ((. Sol.eqPred) . (==) . Sol.eqPred)

instKQ :: Bool
       -> F.SEnv F.Sort
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> [Sol.EQual]
instKQ ho env v t q
  = do (su0, v0) <- candidates senv [(t, [v])] qt
       xs        <- match senv tyss [v0] (So.apply su0 <$> qts)
       return     $ Sol.eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.qParams q
       tyss       = instCands ho env
       senv       = (`F.lookupSEnvWithDistance` env)

instCands :: Bool -> F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands ho env = filter isOk tyss
  where
    tyss      = groupList [(t, x) | (x, t) <- xts]
    isOk      = if ho then const True else isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: So.Env -> [(F.Sort, [F.Symbol])] -> [F.Symbol] -> [F.Sort] -> [[F.Symbol]]
match env tyss xs (t : ts)
  = do (su, x) <- candidates env tyss t
       match env tyss (x : xs) (So.apply su <$> ts)
match _   _   xs []
  = return xs

--------------------------------------------------------------------------------
candidates :: So.Env -> [(F.Sort, [F.Symbol])] -> F.Sort -> [(So.TVSubst, F.Symbol)]
--------------------------------------------------------------------------------
candidates env tyss tx = -- traceShow _msg
    [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx
    _msg  = "candidates tyss :=" ++ F.showpp tyss ++ "tx := " ++ F.showpp tx

--------------------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> Sol.EQual -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = Sol.eqPred eq
    tc            = So.checkSorted env sr -- (F.tracepp _msg sr)
    -- _msg          = printf "okInst: t = %s, eq = %s, env = %s" (F.showpp t) (F.showpp eq) (F.showpp env)


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: F.SolEnv -> Sol.Solution -> F.SimpC a -> F.Expr
lhsPred be s c = F.notracepp _msg $ fst $ apply g s bs
  where
    g          = (ci, be, bs)
    bs         = F.senv c
    ci         = sid c
    _msg       = "LhsPred for id = " ++ show (sid c)

type Cid         = Maybe Integer
type CombinedEnv = (Cid, F.SolEnv, F.IBindEnv)
type ExprInfo    = (F.Expr, KInfo)

apply :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.IBindEnv -> ExprInfo
apply g s bs      = (F.pAnd (pks:ps), kI)
  where
    (pks, kI)     = applyKVars g s ks  -- RJ: switch to applyKVars' to revert to old behavior
    (ps,  ks, _)  = envConcKVars g bs


envConcKVars :: CombinedEnv -> F.IBindEnv -> ([F.Expr], [F.KVSub], [F.KVSub])
envConcKVars g bs = (concat pss, concat kss, L.nubBy (\x y -> F.ksuKVar x == F.ksuKVar y) $ concat gss)
  where
    (pss, kss, gss) = unzip3 [ F.notracepp ("sortedReftConcKVars" ++ F.showpp sr) $ F.sortedReftConcKVars x sr | (x, sr) <- xrs ]
    xrs             = (\i -> F.notracepp  ("lookupBE i := " ++ show i) $ F.lookupBindEnv i be) <$> is
    is              = F.elemsIBindEnv bs
    be              = F.soeBinds (snd3 g)

applyKVars :: CombinedEnv -> Sol.Sol a Sol.QBind -> [F.KVSub] -> ExprInfo
applyKVars g s = mrExprInfos (applyKVar g s) F.pAnd mconcat

applyKVar :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.KVSub -> ExprInfo
applyKVar g s ksu = case Sol.lookup s (F.ksuKVar ksu) of
  Left cs          -> hypPred g s ksu cs
  Right eqs -> (F.pAnd $ fst <$> Sol.qbPreds msg s (F.ksuSubst ksu) eqs, mempty) -- TODO: don't initialize kvars that have a hyp solution
  where
    msg     = "applyKVar: " ++ show (fst3 g)

hypPred :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.KVSub -> Sol.Hyp  -> ExprInfo
hypPred g s ksu = mrExprInfos (cubePred g s ksu) F.pOr mconcatPlus

{- | `cubePred g s k su c` returns the predicate for

        (k . su)

      defined by using cube

        c := [b1,...,bn] |- (k . su')

      in the binder environment `g`.

        bs' := the subset of "extra" binders in [b1...bn] that are *not* in `g`
        p'  := the predicate corresponding to the "extra" binders

 -}

elabExist :: Sol.Sol a Sol.QBind -> [(F.Symbol, F.Sort)] -> F.Expr -> F.Expr
elabExist s xts = F.pExist xts'
  where
    xts'        = [ (x, elab t) | (x, t) <- xts]
    elab        = So.elaborate "elabExist" env
    env         = Sol.sEnv s

cubePred :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.KVSub -> Sol.Cube -> ExprInfo
cubePred g s ksu c    = (elabExist s xts (psu &.& p), kI)
  where
    ((xts,psu,p), kI) = cubePredExc g s ksu c bs'
    bs'               = delCEnv s k bs
    bs                = Sol.cuBinds c
    k                 = F.ksuKVar ksu

type Binders = [(F.Symbol, F.Sort)]

-- | @cubePredExc@ computes the predicate for the subset of binders bs'.
--   The output is a tuple, `(xts, psu, p, kI)` such that the actual predicate
--   we want is `Exists xts. (psu /\ p)`.

cubePredExc :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.KVSub -> Sol.Cube -> F.IBindEnv
            -> ((Binders, F.Pred, F.Pred), KInfo)

cubePredExc g s ksu c bs' = (cubeP, extendKInfo kI (Sol.cuTag c))
  where
    cubeP           = (xts, psu, elabExist s yts' (p' &.& psu') )
    yts'            = symSorts g bs'
    g'              = addCEnv  g bs
    (p', kI)        = apply g' s bs'
    (_  , psu')     = substElim (Sol.sEnv s) sEnv g' k su'
    (xts, psu)      = substElim (Sol.sEnv s) sEnv g  k su
    su'             = Sol.cuSubst c
    bs              = Sol.cuBinds c
    k               = F.ksuKVar   ksu
    su              = F.ksuSubst  ksu
    sEnv            = F.insertSEnv (F.ksuVV ksu) (F.ksuSort ksu) (F.seSort $ Sol.sEnv s)

-- TODO: SUPER SLOW! Decorate all substitutions with Sorts in a SINGLE pass.

{- | @substElim@ returns the binders that must be existentially quantified,
     and the equality predicate relating the kvar-"parameters" and their
     actual values. i.e. given

        K[x1 := e1]...[xn := en]

     where e1 ... en have types t1 ... tn
     we want to quantify out

       x1:t1 ... xn:tn

     and generate the equality predicate && [x1 ~~ e1, ... , xn ~~ en]
     we use ~~ because the param and value may have different sorts, see:

        tests/pos/kvar-param-poly-00.hs

     Finally, we filter out binders if they are

     1. "free" in e1...en i.e. in the outer environment.
        (Hmm, that shouldn't happen...?)

     2. are binders corresponding to sorts (e.g. `a : num`, currently used
        to hack typeclasses current.)
 -}
substElim :: F.SymEnv -> F.SEnv F.Sort -> CombinedEnv -> F.KVar -> F.Subst -> ([(F.Symbol, F.Sort)], F.Pred)
substElim syEnv sEnv g _ (F.Su m) = (xts, p)
  where
    p      = F.pAnd [ mkSubst syEnv x (substSort sEnv frees x t) e t | (x, e, t) <- xets  ]
    xts    = [ (x, t)    | (x, _, t) <- xets, not (S.member x frees) ]
    xets   = [ (x, e, t) | (x, e)    <- xes, t <- sortOf e, not (isClass t)]
    xes    = M.toList m
    env    = combinedSEnv g
    frees  = S.fromList (concatMap (F.syms . snd) xes)
    sortOf = maybeToList . So.checkSortExpr env

substSort :: F.SEnv F.Sort -> S.HashSet F.Symbol -> F.Symbol -> F.Sort -> F.Sort
substSort sEnv _frees x _t = fromMaybe (err x) $ F.lookupSEnv x sEnv
  where
    err x            = error $ "Solution.mkSubst: unknown binder " ++ F.showpp x


-- LH #1091
mkSubst :: F.SymEnv -> F.Symbol -> F.Sort -> F.Expr -> F.Sort -> F.Expr
mkSubst env x tx ey ty
  | tx == ty    = F.EEq ex ey
  | otherwise   = {- F.tracepp _msg -} (F.EEq ex' ey')
  where
    _msg         = "mkSubst-DIFF:" ++ F.showpp (tx, ty) ++ F.showpp (ex', ey')
    ex          = F.expr x
    ex'         = elabToInt env ex tx
    ey'         = elabToInt env ey ty

elabToInt :: F.SymEnv -> F.Expr -> F.Sort -> F.Expr
elabToInt env e s = So.elaborate "elabToInt" env (So.toInt env e s)

isClass :: F.Sort -> Bool
isClass F.FNum  = True
isClass F.FFrac = True
isClass _       = False

--badExpr :: CombinedEnv -> F.KVar -> F.Expr -> a
--badExpr g@(i,_,_) k e
  -- = errorstar $ "substSorts has a badExpr: "
              -- ++ show e
              -- ++ " in cid = "
              -- ++ show i
              -- ++ " for kvar " ++ show k
              -- ++ " in env \n"
              -- ++ show (combinedSEnv g)

-- substPred :: F.Subst -> F.Pred
-- substPred (F.Su m) = F.pAnd [ F.PAtom F.Eq (F.eVar x) e | (x, e) <- M.toList m]

combinedSEnv :: CombinedEnv -> F.SEnv F.Sort
combinedSEnv (_, se, bs) = F.sr_sort <$> F.fromListSEnv (F.envCs be bs)
  where
    be                   = F.soeBinds se

addCEnv :: CombinedEnv -> F.IBindEnv -> CombinedEnv
addCEnv (x, be, bs) bs' = (x, be, F.unionIBindEnv bs bs')

-- delCEnv :: F.IBindEnv -> CombinedEnv -> F.IBindEnv
-- delCEnv bs (_, _, bs')  = F.diffIBindEnv bs bs'

delCEnv :: Sol.Sol a Sol.QBind -> F.KVar -> F.IBindEnv -> F.IBindEnv
delCEnv s k bs  = F.diffIBindEnv bs _kbs
                                                -- ORIG: bs'
  where
    _kbs = safeLookup "delCEnv" k (Sol.sScp s)

symSorts :: CombinedEnv -> F.IBindEnv -> [(F.Symbol, F.Sort)]
symSorts (_, se, _) bs = second F.sr_sort <$> F.envCs be  bs
  where
    be                 = F.soeBinds se

_noKvars :: F.Expr -> Bool
_noKvars = null . V.kvars

--------------------------------------------------------------------------------
-- | Information about size of formula corresponding to an "eliminated" KVar.
--------------------------------------------------------------------------------
data KInfo = KI { kiTags  :: [Tag]
                , kiDepth :: !Int
                , kiCubes :: !Integer
                } deriving (Eq, Ord, Show)

instance Monoid KInfo where
  mempty         = KI [] 0 1
  mappend ki ki' = KI ts d s
    where
      ts         = appendTags (kiTags  ki) (kiTags  ki')
      d          = max        (kiDepth ki) (kiDepth ki')
      s          = (*)        (kiCubes ki) (kiCubes ki')

mplus :: KInfo -> KInfo -> KInfo
mplus ki ki' = (mappend ki ki') { kiCubes = kiCubes ki + kiCubes ki'}

mconcatPlus :: [KInfo] -> KInfo
mconcatPlus = foldr mplus mempty

appendTags :: [Tag] -> [Tag] -> [Tag]
appendTags ts ts' = sortNub (ts ++ ts')

extendKInfo :: KInfo -> F.Tag -> KInfo
extendKInfo ki t = ki { kiTags  = appendTags [t] (kiTags  ki)
                      , kiDepth = 1  +            kiDepth ki }

-- mrExprInfos :: (a -> ExprInfo) -> ([F.Expr] -> F.Expr) -> ([KInfo] -> KInfo) -> [a] -> ExprInfo
mrExprInfos :: (a -> (b, c)) -> ([b] -> b1) -> ([c] -> c1) -> [a] -> (b1, c1)
mrExprInfos mF erF irF xs = (erF es, irF is)
  where
    (es, is)              = unzip $ map mF xs
