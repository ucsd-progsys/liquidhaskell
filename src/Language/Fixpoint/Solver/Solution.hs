{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE PatternGuards     #-}

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
import           Data.Semigroup                 (Semigroup (..))
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import qualified Language.Fixpoint.Misc               as Misc
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types                 ((&.&))
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)
import           Language.Fixpoint.Solver.Sanitize

-- DEBUG
import Text.Printf (printf)
-- import           Debug.Trace


--------------------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------------------
--------------------------------------------------------------------------------
init :: (F.Fixpoint a) => Config -> F.SInfo a -> S.HashSet F.KVar -> Sol.Solution
--------------------------------------------------------------------------------
init cfg si ks = Sol.fromList senv mempty keqs [] mempty ebs xEnv
  where
    keqs       = map (refine si qs genv) ws `using` parList rdeepseq
    qs         = F.quals si
    ws         = [ w | (k, w) <- M.toList (F.ws si), not (isGWfc w) , k `S.member` ks]
    genv       = instConstants si
    senv       = symbolEnv cfg si
    ebs        = ebindInfo si
    xEnv       = F.fromListSEnv [ (x, (i, F.sr_sort sr)) | (i,x,sr) <- F.bindEnvToList (F.bs si)]

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
refineK ho env qs (v, t, k) = F.notracepp _msg (k, eqs')
   where
    eqs                     = instK ho env v t qs
    eqs'                    = Sol.qbFilter (okInst env v t) eqs
    _msg                    = printf "\n\nrefineK: k = %s, eqs = %s" (F.showpp k) (F.showpp eqs)

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
instKQ ho env v t q = do 
  (su0, qsu0, v0) <- candidates senv [(t, [v])] qp
  xs              <- match senv tyss [v0] (applyQP su0 qsu0 <$> qps) 
  return           $ Sol.eQual q (F.notracepp msg (reverse xs))
  where
    msg        = "instKQ " ++ F.showpp (F.qName q) ++ F.showpp (F.qParams q)
    qp : qps   = F.qParams q
    tyss       = instCands ho env
    senv       = (`F.lookupSEnvWithDistance` env)

instCands :: Bool -> F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands ho env = filter isOk tyss
  where
    tyss      = Misc.groupList [(t, x) | (x, t) <- xts]
    isOk      = if ho then const True else isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: So.Env -> [(F.Sort, [F.Symbol])] -> [F.Symbol] -> [F.QualParam] -> [[F.Symbol]]
match env tyss xs (qp : qps)
  = do (su, qsu, x) <- candidates env tyss qp
       match env tyss (x : xs) (applyQP su qsu <$> qps)
match _   _   xs []
  = return xs

applyQP :: So.TVSubst -> QPSubst -> F.QualParam -> F.QualParam
applyQP su qsu qp = qp { qpSort = So.apply     su  (qpSort qp) 
                       , qpPat  = applyQPSubst qsu (qpPat qp) 
                       }

--------------------------------------------------------------------------------
candidates :: So.Env -> [(F.Sort, [F.Symbol])] -> F.QualParam 
           -> [(So.TVSubst, QPSubst, F.Symbol)]
--------------------------------------------------------------------------------
candidates env tyss x = -- traceShow _msg
    [(su, qsu, y) | (t, ys)  <- tyss
                  , su       <- maybeToList (So.unifyFast mono env xt t)
                  , y        <- ys
                  , qsu      <- maybeToList (matchSym x y)                                     
    ]
  where
    xt   = F.qpSort x
    mono = So.isMono xt
    _msg = "candidates tyss :=" ++ F.showpp tyss ++ "tx := " ++ F.showpp xt

matchSym :: F.QualParam -> F.Symbol -> Maybe QPSubst 
matchSym qp y' = case F.qpPat qp of
  F.PatPrefix s i -> JustSub i <$> F.stripPrefix s y 
  F.PatSuffix i s -> JustSub i <$> F.stripSuffix s y 
  F.PatNone       -> Just NoSub 
  F.PatExact s    -> if s == y then Just NoSub else Nothing 
  where 
    y             =  F.tidySymbol y'


data QPSubst = NoSub | JustSub Int F.Symbol  

applyQPSubst :: QPSubst -> F.QualPattern -> F.QualPattern 
applyQPSubst (JustSub i x) (F.PatPrefix s j) 
  | i == j = F.PatExact (F.mappendSym s x) 
applyQPSubst (JustSub i x) (F.PatSuffix j s) 
  | i == j = F.PatExact (F.mappendSym x s) 
applyQPSubst _ p 
  = p 

--------------------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> Sol.EQual -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = Sol.eqPred eq
    tc            = So.checkSorted (F.srcSpan eq) env sr 
    -- _msg          = printf "okInst: t = %s, eq = %s, env = %s" (F.showpp t) (F.showpp eq) (F.showpp env)


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: (F.Loc a) => F.BindEnv -> Sol.Solution -> F.SimpC a -> F.Expr
lhsPred be s c = F.notracepp _msg $ fst $ apply g s bs
  where
    g          = CEnv ci be bs (F.srcSpan c)
    bs         = F.senv c
    ci         = sid c
    _msg       = "LhsPred for id = " ++ show (sid c) ++ " with SOLUTION = " ++ F.showpp s

data CombinedEnv = CEnv 
  { ceCid  :: !Cid
  , ceBEnv :: !F.BindEnv
  , ceIEnv :: !F.IBindEnv 
  , ceSpan :: !F.SrcSpan
  }

instance F.Loc CombinedEnv where 
  srcSpan = ceSpan

type Cid         = Maybe Integer
type ExprInfo    = (F.Expr, KInfo)

apply :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.IBindEnv -> ExprInfo
apply g s bs      = (F.pAnd (pks:ps), kI)
  where
    (pks, kI)     = applyKVars g s ks  
    (ps,  ks, _)  = envConcKVars g s bs


envConcKVars :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.IBindEnv -> ([F.Expr], [F.KVSub], [F.KVSub])
envConcKVars g s bs = (concat pss, concat kss, L.nubBy (\x y -> F.ksuKVar x == F.ksuKVar y) $ concat gss)
  where
    (pss, kss, gss) = unzip3 [ F.notracepp ("sortedReftConcKVars" ++ F.showpp sr) $ F.sortedReftConcKVars x sr | (x, sr) <- xrs ]
    xrs             = lookupBindEnvExt g s <$> is
    is              = F.elemsIBindEnv bs

lookupBindEnvExt :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.BindId -> (F.Symbol, F.SortedReft)
lookupBindEnvExt g s i 
  | Just p <- ebSol g s i = (x, sr { F.sr_reft = F.Reft (x, p) }) 
  | otherwise             = (x, sr)
   where 
      (x, sr)              = F.lookupBindEnv i (ceBEnv g) 

ebSol :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.BindId -> Maybe F.Expr
ebSol g s i = case  M.lookup i sebds of
  Just (Sol.EbSol p)    -> Just p
  Just (Sol.EbDef cs _) -> Just $ F.PAnd (cSol <$> cs)
  _                     -> Nothing
  where
    sebds = Sol.sEbd s

    ebReft s (i,c) = exElim (Sol.sxEnv s) (senv c) i (ebindReft g s c)
    cSol c = if sid c == ceCid g 
                then F.PFalse
                else ebReft s' (i, c)

    s' = s { Sol.sEbd = M.insert i Sol.EbIncr sebds }

ebindReft :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.SimpC () -> F.Pred
ebindReft g s c = F.pAnd [ fst $ apply g' s bs, F.crhs c ]
  where
    g'          = g { ceCid = sid c, ceIEnv = bs } 
    bs          = F.senv c

exElim :: F.SEnv (F.BindId, F.Sort) -> F.IBindEnv -> F.BindId -> F.Pred -> F.Pred
exElim env ienv xi p = F.notracepp msg (F.pExist yts p)
  where
    msg         = "exElim" -- printf "exElim: ix = %d, p = %s" xi (F.showpp p)
    yts         = [ (y, yt) | y        <- F.syms p
                            , (yi, yt) <- maybeToList (F.lookupSEnv y env)
                            , xi < yi
                            , yi `F.memberIBindEnv` ienv                  ]

applyKVars :: CombinedEnv -> Sol.Sol a Sol.QBind -> [F.KVSub] -> ExprInfo
applyKVars g s = mrExprInfos (applyKVar g s) F.pAnd mconcat

applyKVar :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.KVSub -> ExprInfo
applyKVar g s ksu = case Sol.lookup s (F.ksuKVar ksu) of
  Left cs   -> hypPred g s ksu cs
  Right eqs -> (F.pAnd $ fst <$> Sol.qbPreds msg s (F.ksuSubst ksu) eqs, mempty) -- TODO: don't initialize kvars that have a hyp solution
  where
    msg     = "applyKVar: " ++ show (ceCid g)

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

elabExist :: F.SrcSpan -> Sol.Sol a Sol.QBind -> [(F.Symbol, F.Sort)] -> F.Expr -> F.Expr
elabExist sp s xts p = F.pExist xts' p
  where
    xts'        = [ (x, elab t) | (x, t) <- xts]
    elab        = So.elaborate (F.atLoc sp "elabExist") env
    env         = Sol.sEnv s

cubePred :: CombinedEnv -> Sol.Sol a Sol.QBind -> F.KVSub -> Sol.Cube -> ExprInfo
cubePred g s ksu c    = (F.notracepp "cubePred" $ elabExist sp s xts (psu &.& p), kI)
  where
    sp                = F.srcSpan g
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
    cubeP           = (xts, psu, elabExist sp s yts' (p' &.& psu') )
    sp              = F.srcSpan g
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
    p      = F.pAnd [ mkSubst sp syEnv x (substSort sEnv frees x t) e t | (x, e, t) <- xets  ]
    xts    = [ (x, t)    | (x, _, t) <- xets, not (S.member x frees) ]
    xets   = [ (x, e, t) | (x, e)    <- xes, t <- sortOf e, not (isClass t)]
    xes    = M.toList m
    env    = combinedSEnv g
    frees  = S.fromList (concatMap (F.syms . snd) xes)
    sortOf = maybeToList . So.checkSortExpr sp env
    sp     = F.srcSpan g

substSort :: F.SEnv F.Sort -> S.HashSet F.Symbol -> F.Symbol -> F.Sort -> F.Sort
substSort sEnv _frees x _t = fromMaybe (err x) $ F.lookupSEnv x sEnv
  where
    err x            = error $ "Solution.mkSubst: unknown binder " ++ F.showpp x


-- LH #1091
mkSubst :: F.SrcSpan -> F.SymEnv -> F.Symbol -> F.Sort -> F.Expr -> F.Sort -> F.Expr
mkSubst sp env x tx ey ty
  | tx == ty    = F.EEq ex ey
  | otherwise   = {- F.tracepp _msg -} (F.EEq ex' ey')
  where
    _msg         = "mkSubst-DIFF:" ++ F.showpp (tx, ty) ++ F.showpp (ex', ey')
    ex          = F.expr x
    ex'         = elabToInt sp env ex tx
    ey'         = elabToInt sp env ey ty

elabToInt :: F.SrcSpan -> F.SymEnv -> F.Expr -> F.Sort -> F.Expr
elabToInt sp env e s = So.elaborate (F.atLoc sp "elabToInt") env (So.toInt env e s)

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
combinedSEnv g = F.sr_sort <$> F.fromListSEnv (F.envCs be bs)
  where 
    be         = ceBEnv g 
    bs         = ceIEnv g 

addCEnv :: CombinedEnv -> F.IBindEnv -> CombinedEnv
addCEnv g bs' = g { ceIEnv = F.unionIBindEnv (ceIEnv g) bs' }
-- addCEnv (x, be, bs) bs' = (x, be, F.unionIBindEnv bs bs')


delCEnv :: Sol.Sol a Sol.QBind -> F.KVar -> F.IBindEnv -> F.IBindEnv
delCEnv s k bs = F.diffIBindEnv bs _kbs
  where
    _kbs       = Misc.safeLookup "delCEnv" k (Sol.sScp s)

symSorts :: CombinedEnv -> F.IBindEnv -> [(F.Symbol, F.Sort)]
symSorts g bs = second F.sr_sort <$> F.envCs (ceBEnv g) bs

_noKvars :: F.Expr -> Bool
_noKvars = null . V.kvars

--------------------------------------------------------------------------------
-- | Information about size of formula corresponding to an "eliminated" KVar.
--------------------------------------------------------------------------------
data KInfo = KI { kiTags  :: [Tag]
                , kiDepth :: !Int
                , kiCubes :: !Integer
                } deriving (Eq, Ord, Show)

instance Semigroup KInfo where
  ki <> ki' = KI ts d s
    where
      ts         = appendTags (kiTags  ki) (kiTags  ki')
      d          = max        (kiDepth ki) (kiDepth ki')
      s          = (*)        (kiCubes ki) (kiCubes ki')

instance Monoid KInfo where
  mempty  = KI [] 0 1
  mappend = (<>)

mplus :: KInfo -> KInfo -> KInfo
mplus ki ki' = (mappend ki ki') { kiCubes = kiCubes ki + kiCubes ki'}

mconcatPlus :: [KInfo] -> KInfo
mconcatPlus = foldr mplus mempty

appendTags :: [Tag] -> [Tag] -> [Tag]
appendTags ts ts' = Misc.sortNub (ts ++ ts')

extendKInfo :: KInfo -> F.Tag -> KInfo
extendKInfo ki t = ki { kiTags  = appendTags [t] (kiTags  ki)
                      , kiDepth = 1  +            kiDepth ki }

-- mrExprInfos :: (a -> ExprInfo) -> ([F.Expr] -> F.Expr) -> ([KInfo] -> KInfo) -> [a] -> ExprInfo
mrExprInfos :: (a -> (b, c)) -> ([b] -> b1) -> ([c] -> c1) -> [a] -> (b1, c1)
mrExprInfos mF erF irF xs = (erF es, irF is)
  where
    (es, is)              = unzip $ map mF xs

--------------------------------------------------------------------------------
-- | `ebindInfo` constructs the information about the "ebind-definitions". 
--------------------------------------------------------------------------------
ebindInfo :: F.SInfo a -> [(F.BindId, Sol.EbindSol)]
ebindInfo si = group [((bid, x), cons cid) | (bid, cid, x) <- ebindDefs si]
  where cons cid = const () <$> Misc.safeLookup "ebindInfo" cid cs
        cs = F.cm si
        cmpByFst x y = fst ( fst x ) == fst ( fst y )
        group xs = (\ys -> ( (fst $ fst $ head ys)
                           , Sol.EbDef (snd <$> ys) (snd $ fst $ head ys)))
                    <$> L.groupBy cmpByFst xs

ebindDefs :: F.SInfo a -> [(F.BindId, F.SubcId, F.Symbol)]
ebindDefs si = [ (bid, cid, x) | (cid, x) <- cDefs
                               , bid      <- maybeToList (M.lookup x ebSyms)]
  where 
    ebSyms   = ebindSyms si 
    cDefs    = cstrDefs  si 

ebindSyms :: F.SInfo a -> M.HashMap F.Symbol F.BindId
ebindSyms si = M.fromList [ (xi, bi) | bi        <- ebinds si
                                     , let (xi,_) = F.lookupBindEnv bi be ] 
  where
    be       = F.bs si 
 
cstrDefs :: F.SInfo a -> [(F.SubcId, F.Symbol)]
cstrDefs si = [(cid, x) | (cid, c) <- M.toList (cm si)
                        , x <- maybeToList (cstrDef be c) ]
  where 
    be      = F.bs si

cstrDef :: F.BindEnv -> F.SimpC a -> Maybe F.Symbol 
cstrDef be c 
  | Just (F.EVar x) <- e = Just x 
  | otherwise            = Nothing 
  where 
    (v,_)              = F.lookupBindEnv (cbind c) be 
    e                  = F.notracepp _msg $ F.isSingletonExpr v rhs 
    _msg                = "cstrDef: " ++ show (stag c) ++ " crhs = " ++ F.showpp rhs 
    rhs                = V.stripCasts (crhs c)

