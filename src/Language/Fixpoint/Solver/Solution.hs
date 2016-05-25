{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}

module Language.Fixpoint.Solver.Solution
        ( -- * Create and Update Solution
          init, update

          -- * Lookup Solution
        , lhsPred
        , noKvars

        )
where

import           Control.Parallel.Strategies
import           Control.Arrow (second)
import qualified Data.HashSet                   as S
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Data.Either                    (lefts, rights)
-- import           Language.Fixpoint.Utils.Files
-- import           Language.Fixpoint.Types.Config
-- import           Language.Fixpoint.Graph
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types.Constraints hiding (ws, bs)
import           Prelude                        hiding (init, lookup)

-- DEBUG
-- import Text.Printf (printf)
import           Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier ----------------------------------------
--------------------------------------------------------------------------------

-- mkJVar :: F.Expr -> QBind
-- mkJVar p = [F.EQL dummyQual p []]

-- dummyQual :: F.Qualifier
-- dummyQual = F.Q F.nonSymbol [] F.PFalse (F.dummyPos "")

--------------------------------------------------------------------------------
-- | Update Solution -----------------------------------------------------------
--------------------------------------------------------------------------------
update :: Solution -> [F.KVar] -> [(F.KVar, F.EQual)] -> (Bool, Solution)
-------------------------------------------------------------------------
update s ks kqs = {- tracepp msg -} (or bs, s')
  where
    kqss        = groupKs ks kqs
    (bs, s')    = folds update1 s kqss
    -- msg         = printf "ks = %s, s = %s" (showpp ks) (showpp s)

folds   :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
folds f b = L.foldl' step ([], b)
  where
     step (cs, acc) x = (c:cs, x')
       where
         (c, x')      = f acc x

groupKs :: [F.KVar] -> [(F.KVar, F.EQual)] -> [(F.KVar, QBind)]
groupKs ks kqs = M.toList $ groupBase m0 kqs
  where
    m0         = M.fromList $ (,[]) <$> ks

update1 :: Solution -> (F.KVar, QBind) -> (Bool, Solution)
update1 s (k, qs) = (change, solInsert k qs s)
  where
    oldQs         = F.solLookupQBind s k
    change        = length oldQs /= length qs

--------------------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------------------
--------------------------------------------------------------------------------
init :: F.SInfo a -> S.HashSet F.KVar -> Solution
--------------------------------------------------------------------------------
init si ks = F.solFromList keqs []
  where
    keqs   = map (refine si qs) ws `using` parList rdeepseq
    qs     = F.quals si
    ws     = [ w | (k, w) <- M.toList (F.ws si), k `S.member` ks]

--------------------------------------------------------------------------------
refine :: F.SInfo a
       -> [F.Qualifier]
       -> F.WfC a
       -> (F.KVar, QBind)
refine fi qs w = refineK (allowHOquals fi) env qs $ F.wrft w
  where
    env        = wenv <> genv
    wenv       = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))
    genv       = F.lits fi

refineK :: Bool -> F.SEnv F.Sort -> [F.Qualifier] -> (F.Symbol, F.Sort, F.KVar) -> (F.KVar, QBind)
refineK ho env qs (v, t, k) = {- tracepp msg -} (k, eqs')
   where
    eqs                  = instK ho env v t qs
    eqs'                 = filter (okInst env v t) eqs
    -- msg                  = printf "refineK: k = %s, eqs = %s" (showpp k) (showpp eqs)

--------------------------------------------------------------------------------
instK :: Bool
      -> F.SEnv F.Sort
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> QBind
--------------------------------------------------------------------------------
instK ho env v t = unique . concatMap (instKQ ho env v t)
  where
    unique       = L.nubBy ((. F.eqPred) . (==) . F.eqPred)

instKQ :: Bool
       -> F.SEnv F.Sort
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> QBind
instKQ ho env v t q
  = do (su0, v0) <- candidates senv [(t, [v])] qt
       xs        <- match senv tyss [v0] (So.apply su0 <$> qts)
       return     $ F.eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.q_params q
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
candidates env tyss tx
  = [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

--------------------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> F.EQual -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = F.eqPred eq
    tc            = So.checkSorted env sr


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: F.SolEnv -> F.Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred be s c = {- F.tracepp msg $ -} fst $ apply g s bs
  where
    g          = (ci, be, bs)
    bs         = F.senv c
    ci         = sid c
    -- msg        = "LhsPred for id = " ++ show (sid c)

type Cid         = Maybe Integer
type CombinedEnv = (Cid, F.SolEnv, F.IBindEnv)
type ExprInfo    = (F.Expr, KInfo)
type KVSub       = (F.KVar, F.Subst)

apply :: CombinedEnv -> Solution -> F.IBindEnv -> ExprInfo
apply g s bs  = (F.pAnd (pks : ps), kI)
  where
    (pks, kI) = applyKVars g s ks  -- RJ: switch to applyKVars' to revert to old behavior
    (ks, ps)  = mapEither exprKind es
    es        = concatMap (bindExprs g) (F.elemsIBindEnv bs)

exprKind :: F.Expr -> Either KVSub F.Expr
exprKind (F.PKVar k su) = Left  (k, su)
exprKind p              = Right p

bindExprs :: CombinedEnv -> F.BindId -> [F.Expr]
bindExprs (_,be,_) i = [p `F.subst1` (v, F.eVar x) | F.Reft (v, p) <- rs ]
  where
    (x, sr)          = F.lookupBindEnv i (F.soeBinds be)
    rs               = F.reftConjuncts $ F.sr_reft sr

applyKVars :: CombinedEnv -> Solution -> [KVSub] -> ExprInfo
applyKVars g s = mrExprInfos (applyPack g s) F.pAnd mconcat . packKVars g
  where
    applyPack :: CombinedEnv -> Solution -> [KVSub] -> ExprInfo
    applyPack g s kvs = case packable s kvs of
      Nothing       -> applyKVars' g s kvs
      Just (p, [])  -> (p, mempty)
      Just (p, kcs) -> applyPackCubes g s p kcs
    _tr kvs kcs
       | length kvs > 1 = trace ("PACKING" ++ F.showpp kvs) kcs
       | otherwise      = kcs


--------------------------------------------------------------------------------
applyPackCubes :: CombinedEnv -> Solution -> F.Expr -> ListNE (KVSub, F.Cube) -> ExprInfo
--------------------------------------------------------------------------------
applyPackCubes g s p kcs = mrExprInfos (applyPackCube g'' s) conjF catF kcs
  where
    conjF                = (p &.&) . conjCube yts'' p''
    catF kIs             = mconcat (kI : kIs)
    yts''                = symSorts g bs''
    (p'', kI)            = apply g'' s bs''
    g''                  = addCEnv g bs''
    bs''                 = foldr1 F.intersectionIBindEnv bs's
    bs's                 = [ delCEnv bs g | bs <- F.cuBinds . snd <$> kcs ]

conjCube :: Binders -> F.Pred -> [(Binders, F.Pred, F.Pred)] -> F.Pred
conjCube yts'' p'' z     = foldr wrap inP xtSuPs
  where
    wrap (xts, suP) q    = F.pExist xts (suP &.& q)
    xtSuPs               = [ (xts, psu) | (xts, psu, _) <- z ]
    inP                  = F.pExist yts'' (F.pAnd (p'' : (thd3 <$> z)))

applyPackCube :: CombinedEnv
              -> Solution
              -> (KVSub, F.Cube)
              -> ((Binders, F.Pred, F.Pred), KInfo)
applyPackCube g s kc = cubePredExc g s k su c bs'
  where
    ((k, su), c)     = kc
    bs'              = delCEnv bs g
    bs               = F.cuBinds c

applyKVars' :: CombinedEnv -> Solution -> [KVSub] -> ExprInfo
applyKVars' g s = mrExprInfos (applyKVar g s) F.pAnd mconcat

applyKVar :: CombinedEnv -> Solution -> KVSub -> ExprInfo
applyKVar g s (k, su) = case F.solLookup s k of
  Left cs   -> hypPred g s k su cs
  Right eqs -> (qBindPred su eqs, mempty) -- TODO: don't initialize kvars that have a hyp solution

hypPred :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Hyp  -> ExprInfo
hypPred g s k su = mrExprInfos (cubePred g s k su) F.pOr mconcatPlus


{- | `cubePred g s k su c` returns the predicate for

        (k . su)

      defined by using cube

        c := [b1,...,bn] |- (k . su')

      in the binder environment `g`.

        bs' := the subset of "extra" binders in [b1...bn] that are *not* in `g`
        p'  := the predicate corresponding to the "extra" binders

 -}

(&.&) :: F.Pred -> F.Pred -> F.Pred
(&.&) p q = F.pAnd [p, q]

cubePred :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Cube -> ExprInfo
cubePred g s k su c   = ( F.pExist xts (psu &.& p) , kI )
  where
    ((xts,psu,p), kI) = cubePredExc g s k su c bs'
    bs'               = delCEnv bs g
    bs                = F.cuBinds c

type Binders = [(F.Symbol, F.Sort)]

-- | @cubePredExc@ computes the predicate for the subset of binders bs'.
--   The output is a tuple, `(xts, psu, p, kI)` such that the actual predicate
--   we want is `Exists xts. (psu /\ p)`.

cubePredExc :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Cube -> F.IBindEnv
            -> ((Binders, F.Pred, F.Pred), KInfo)

cubePredExc g s k su c bs' = (cubeP, extendKInfo kI (cuTag c))
  where
    cubeP           = ( xts, psu, F.pExist yts' (p' &.& psu') )
    yts'            = symSorts g bs'
    g'              = addCEnv  g bs
    (p', kI)        = apply g' s bs'
    (_  , psu')     = substElim g' k su'
    (xts, psu)      = substElim g  k su
    su'             = F.cuSubst c
    bs              = F.cuBinds c



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
substElim :: CombinedEnv -> F.KVar -> F.Subst -> ([(F.Symbol, F.Sort)], F.Pred)
substElim g _ (F.Su m) = (xts, p)
  where
    p      = F.pAnd [ F.PAtom F.Ueq (F.eVar x) e | (x, e, _) <- xets  ]
    xts    = [ (x, t)    | (x, _, t) <- xets, not (S.member x frees) ]
    xets   = [ (x, e, t) | (x, e)    <- xes, t <- sortOf e, not (isClass t) ]
    xes    = M.toList m
    env    = combinedSEnv g
    frees  = S.fromList (concatMap (F.syms . snd) xes)
    sortOf = maybeToList . So.checkSortExpr env

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

delCEnv :: F.IBindEnv -> CombinedEnv -> F.IBindEnv
delCEnv bs (_, _, bs')  = F.diffIBindEnv bs bs'

symSorts :: CombinedEnv -> F.IBindEnv -> [(F.Symbol, F.Sort)]
symSorts (_, se, _) bs = second F.sr_sort <$> F.envCs be  bs
  where
    be                 = F.soeBinds se

noKvars :: F.Expr -> Bool
noKvars = null . V.kvars

--------------------------------------------------------------------------------
qBindPred :: F.Subst -> QBind -> F.Expr
--------------------------------------------------------------------------------
qBindPred su = F.subst su . F.pAnd . fmap F.eqPred

--------------------------------------------------------------------------------
packKVars :: CombinedEnv -> [KVSub] -> [[KVSub]]
--------------------------------------------------------------------------------
packKVars (_, se, _)   = concatMap eF . M.toList . groupMap kF
  where
    sm                 = F.soePacks se
    kF (k, _)          = F.getPack k sm
    eF (Just _,  xs)   = [xs]
    eF (Nothing, xs)   = singleton <$> xs

--------------------------------------------------------------------------------
packable :: Solution -> [KVSub] -> Maybe (F.Expr, [(KVSub, F.Cube)])
--------------------------------------------------------------------------------
packable s = fmap reduceCubes . sequence . fmap (getCube s)

reduceCubes :: [Either F.Expr (KVSub, F.Cube)] -> (F.Expr, [(KVSub, F.Cube)])
reduceCubes zs = (F.pAnd ps, cs)
  where
    ps         = lefts  zs
    cs         = rights zs

getCube :: Solution -> KVSub -> Maybe (Either F.Expr (KVSub, F.Cube))
getCube s (k, su) = case F.solLookup s k of
  Left []   -> Just (Left F.PFalse)
  Left [c]  -> Just (Right ((k, su), c))
  Right eqs -> Just (Left  (qBindPred su eqs))
  _         -> Nothing




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
