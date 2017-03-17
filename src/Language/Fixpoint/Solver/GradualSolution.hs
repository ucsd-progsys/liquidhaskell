{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}

module Language.Fixpoint.Solver.GradualSolution
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
import           Data.Maybe                     (fromMaybe, maybeToList, isNothing, catMaybes)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Smt.Theories       as Thy
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types                 ((&.&))
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)
import           Language.Fixpoint.Solver.Sanitize


--------------------------------------------------------------------------------
-- | Initial Gradual Solution (from Qualifiers and WF constraints) -------------
--------------------------------------------------------------------------------
init :: Config -> F.SInfo a -> S.HashSet F.KVar -> Sol.GSolution
--------------------------------------------------------------------------------
init cfg si ks = Sol.fromList senv geqs keqs [] mempty
  where
    keqs       = map (refine si qs genv)  ws `using` parList rdeepseq
    geqs       = map (refineG si qs genv) gs `using` parList rdeepseq 
    qs         = F.quals si
    ws         = [ w | (k, w) <- ws0, k `S.member` ks]
    gs         = snd <$> gs0
    genv       = instConstants si
    senv       = symbolEnv cfg si

    (gs0,ws0)  = L.partition (isGWfc . snd) $ M.toList (F.ws si)


--------------------------------------------------------------------------------
refineG :: F.SInfo a -> [F.Qualifier] -> F.SEnv F.Sort -> F.WfC a -> (F.KVar, (((F.Symbol,F.Sort), F.Expr), Sol.GBind))
refineG fi qs genv w = (k, (((fst3 $ wrft w, snd3 $ wrft w), wexpr w), Sol.qbToGb qb))
  where 
    (k, qb) = refine fi qs genv w 

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
refineK ho env qs (v, t, k) = (k, eqs')
   where
    eqs                     = instK ho env v t qs
    eqs'                    = Sol.qbFilter (okInst env v t) eqs

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
candidates env tyss tx = 
    [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

--------------------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> Sol.EQual -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = Sol.eqPred eq
    tc            = So.checkSorted env sr 


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: F.SolEnv -> Sol.GSolution -> F.SimpC a ->  [([(F.KVar, Sol.QBind)], F.Expr)]
lhsPred be s c = gSelectToList (fst <$> applyGradual g s bs)
  where
    g                 = (ci, be, bs)
    bs                = F.senv c
    ci                = sid c

type Cid         = Maybe Integer
type CombinedEnv = (Cid, F.SolEnv, F.IBindEnv)
type ExprInfo    = (F.Expr, KInfo)

applyGradual        :: CombinedEnv -> Sol.GSolution -> F.IBindEnv -> GSelect ExprInfo
applyGradual g s bs = mappendGSelect mappendExprInfo pks (applyKVarsGrad g s ks)
  where
    pgs           = allCombinations $ applyGVars g s gs
    pks           = if null gs 
                        then GNone (F.pAnd ps, mempty) 
                        else GOpt [(fst (unzip l) , (F.pAnd (ps++snd (unzip l)), mempty)) | l <- pgs ]
    (ps,  ks, gs) = envConcKVars g bs

    mappendExprInfo (e1, i1) (e2, i2) = (F.pAnd [e1, e2], mappend i1 i2)


envConcKVars :: CombinedEnv -> F.IBindEnv -> ([F.Expr], [F.KVSub], [F.KVSub])
envConcKVars g bs = (concat pss, concat kss, L.nubBy (\x y -> F.ksuKVar x == F.ksuKVar y) $ concat gss)
  where
    (pss, kss, gss) = unzip3 [ F.sortedReftConcKVars x sr | (x, sr) <- xrs ]
    xrs             = (\i -> F.lookupBindEnv i be) <$> is
    is              = F.elemsIBindEnv bs
    be              = F.soeBinds (snd3 g)

applyGVars :: CombinedEnv -> Sol.GSolution -> [F.KVSub] -> [[((F.KVar, Sol.QBind), F.Expr)]]
applyGVars g s = map (applyGVar g s)


applyGVar :: CombinedEnv -> Sol.GSolution -> F.KVSub -> [((F.KVar, Sol.QBind), F.Expr)]
applyGVar g s ksu = case Sol.glookup s (F.ksuKVar ksu) of
  Right (Right (e,eqss)) -> [((F.ksuKVar ksu, eqs), F.pAnd ((F.subst su (snd e)):(fst <$> Sol.qbPreds msg s su eqs))) | eqs <- Sol.gbToQbs eqss]
  _                      -> []
  where
    msg     = "applyGVar: " ++ show (fst3 g)
    su      = F.ksuSubst ksu

applyKVarsGrad :: CombinedEnv -> Sol.GSolution -> [F.KVSub] -> GSelect ExprInfo
applyKVarsGrad g s xs = (f <$> (collapseGSelect $ map (applyKVarGrad g s) xs))
  where
    f xs = let (es, is) = unzip xs  in (F.pAnd es, mconcat is)

applyKVarGrad :: CombinedEnv -> Sol.GSolution -> F.KVSub -> GSelect ExprInfo
applyKVarGrad g s ksu = case Sol.glookup s (F.ksuKVar ksu) of
  Left cs                -> hypPredGrad g s ksu cs
  Right (Left eqs)       -> GNone (F.pAnd $ fst <$> Sol.qbPreds msg s (F.ksuSubst ksu) eqs, mempty)
  Right (Right (e,eqss)) -> GOpt [([(F.ksuKVar ksu, eqs)]
                                  , (, mempty) $ F.pAnd ((F.subst su (snd e)):(fst <$> Sol.qbPreds msg s su eqs))) 
                                  | eqs <- Sol.gbToQbs eqss]
  where
    msg     = "applyKVar: " ++ show (fst3 g) 
    su      = F.ksuSubst ksu


hypPredGrad :: CombinedEnv -> Sol.GSolution -> F.KVSub -> Sol.Hyp  -> GSelect ExprInfo
hypPredGrad g s ksu xs = f <$> (collapseGSelect $ map (cubePredGrad g s ksu) xs)
  where
    f xs = let (es, is) = unzip xs  in (F.pOr es, mconcatPlus is)


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


cubePredGrad :: CombinedEnv -> Sol.GSolution -> F.KVSub -> Sol.Cube -> GSelect ExprInfo
cubePredGrad g s ksu c  = ((\((xts,psu,p), kI) -> (elabExist s xts (psu &.& p) , kI)) <$> cubePredExcGrad g s ksu c bs')
  where
    bs'               = delCEnv s k bs
    bs                = Sol.cuBinds c
    k                 = F.ksuKVar ksu


type Binders = [(F.Symbol, F.Sort)]

-- | @cubePredExc@ computes the predicate for the subset of binders bs'.
--   The output is a tuple, `(xts, psu, p, kI)` such that the actual predicate
--   we want is `Exists xts. (psu /\ p)`.


cubePredExcGrad :: CombinedEnv -> Sol.GSolution -> F.KVSub -> Sol.Cube -> F.IBindEnv
            -> GSelect ((Binders, F.Pred, F.Pred), KInfo)
cubePredExcGrad g s ksu c bs' 
  = f <$> (applyGradual g' s bs')
  where
    f (p', kI)      = ((xts, psu, elabExist s yts' (p' &.& psu') ), extendKInfo kI (Sol.cuTag c))
    yts'            = symSorts g bs'
    g'              = addCEnv  g bs
    
    (_  , psu')     = substElim sEnv g' k su'
    (xts, psu)      = substElim sEnv g  k su
    su'             = Sol.cuSubst c
    bs              = Sol.cuBinds c
    k               = F.ksuKVar   ksu
    su              = F.ksuSubst  ksu
    sEnv            = F.insertSEnv (F.ksuVV ksu) (F.ksuSort ksu) (Sol.sEnv s)


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
substElim :: F.SEnv F.Sort -> CombinedEnv -> F.KVar -> F.Subst -> ([(F.Symbol, F.Sort)], F.Pred)
substElim sEnv g _ (F.Su m) = (xts, p)
  where
    p      = F.pAnd [ mkSubst x (substSort sEnv frees x t) e t | (x, e, t) <- xets  ]
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

mkSubst :: F.Symbol -> F.Sort -> F.Expr -> F.Sort -> F.Expr
mkSubst x tx ey ty
  | tx == ty    = F.EEq ex ey
  | otherwise   = F.notracepp msg (F.EEq ex' ey')
  where
    msg         = "mkSubst-DIFF:" ++ F.showpp (tx, ty) ++ F.showpp (ex', ey')
    ex          = F.expr x
    ex'         = Thy.toInt ex tx
    ey'         = Thy.toInt ey ty

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


--------------------------------------------------------------------------------
-- | Gradual Selection Interface -----------------------------------------------
--------------------------------------------------------------------------------
data GSelect a = GNone a | GOpt [([(F.KVar, Sol.QBind)], a)] deriving (Show)


gSelectToList :: GSelect a -> [([(F.KVar, Sol.QBind)], a)]
gSelectToList (GNone a) = [([], a)]
gSelectToList (GOpt xs) = xs 


instance Functor GSelect where
  fmap f (GNone a) = GNone  (f a)
  fmap f (GOpt xs) = GOpt [(p, f a) | (p, a) <- xs]

mappendGSelect :: (a -> a -> b) -> GSelect a -> GSelect a -> GSelect b 
mappendGSelect f (GNone x) (GNone y) = GNone (f x y)
mappendGSelect f (GNone x) (GOpt ys) = GOpt [(i, f x y) | (i, y) <- ys] 
mappendGSelect f (GOpt xs) (GNone y) = GOpt [(i, f x y) | (i, x) <- xs]
mappendGSelect f (GOpt xs) (GOpt ys) = GOpt $ concatMap (\y -> (catMaybes $ map (\x -> g x y) xs)) ys 
  where
    g (xs, x) (ys, y)
      | null [ () | (k1, _) <- xs, (k2, _) <- ys, k1 == k2 ]  
      =  Just (xs ++ ys, f x y)
      | and [v1 == v2 | (k1, v1) <- xs, (k2, v2) <- ys, k1 == k2 ] 
      = Just (xs ++ [(k, v) | (k, v) <- ys, not (k `elem` (fst <$> xs))], f x y)
      | otherwise
      = Nothing 

collapseGSelect :: [GSelect a] -> GSelect [a]
collapseGSelect = foldl (mappendGSelect (\x y -> (x ++ y))) (GNone []) . fmap (fmap (:[]))

