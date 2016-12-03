{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Fixpoint.Types.Visitor (
  -- * Visitor
     Visitor (..)
  ,  Visitable (..)

  -- * Extracting Symbolic Constants (String Literals)
  ,  SymConsts (..)

  -- * Default Visitor
  , defaultVisitor

  -- * Transformers
  , trans

  -- * Accumulators
  , fold

  -- * Clients
  , kvars
  , size, lamSize
  , envKVars
  , envKVarsN
  , rhsKVars
  , mapKVars, mapKVars', mapKVarSubsts
  , mapExpr, mapMExpr

  -- * Predicates on Constraints
  , isConcC , isKvarC

  -- * Sorts
  , foldSort, mapSort


  ) where

import           Control.Monad.Trans.State.Strict (State, modify, runState)
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import qualified Data.List           as L
import           Language.Fixpoint.Types hiding (mapSort)
import           Language.Fixpoint.Misc (count, sortNub)

data Visitor acc ctx = Visitor {
 -- | Context @ctx@ is built in a "top-down" fashion; not "across" siblings
    ctxExpr :: ctx -> Expr -> ctx

  -- | Transforms can access current @ctx@
  , txExpr  :: ctx -> Expr -> Expr

  -- | Accumulations can access current @ctx@; @acc@ value is monoidal
  , accExpr :: ctx -> Expr -> acc
  }

---------------------------------------------------------------------------------
defaultVisitor :: Monoid acc => Visitor acc ctx
---------------------------------------------------------------------------------
defaultVisitor = Visitor {
    ctxExpr    = const -- \c _ -> c
  , txExpr     = \_ x -> x
  , accExpr    = \_ _ -> mempty
  }

------------------------------------------------------------------------

fold         :: (Visitable t, Monoid a) => Visitor a ctx -> ctx -> a -> t -> a
fold v c a t = snd $ execVisitM v c a visit t

trans        :: (Visitable t, Monoid a) => Visitor a ctx -> ctx -> a -> t -> t
trans v c _ z = fst $ execVisitM v c mempty visit z

execVisitM :: Visitor a ctx -> ctx -> a -> (Visitor a ctx -> ctx -> t -> State a t) -> t -> (t, a)
execVisitM v c a f x = runState (f v c x) a

type VisitM acc = State acc

accum :: (Monoid a) => a -> VisitM a ()
accum = modify . mappend

(<$$>) ::  (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
f <$$> x = traverse f x

------------------------------------------------------------------------------
class Visitable t where
  visit :: (Monoid a) => Visitor a c -> c -> t -> VisitM a t

instance Visitable Expr where
  visit = visitExpr

instance Visitable Reft where
  visit v c (Reft (x, ra)) = (Reft . (x, )) <$> visit v c ra

instance Visitable SortedReft where
  visit v c (RR t r) = RR t <$> visit v c r

instance Visitable (Symbol, SortedReft) where
  visit v c (sym, sr) = (sym, ) <$> visit v c sr

instance Visitable BindEnv where
  visit v c = mapM (visit v c)

---------------------------------------------------------------------------------
-- Warning: these instances were written for mapKVars over GInfos only;
--  check that they behave as expected before using with other clients.
instance Visitable (SimpC a) where
  visit v c x = do
    rhs' <- visit v c (_crhs x)
    return x { _crhs = rhs' }

instance Visitable (SubC a) where
  visit v c x = do
    lhs' <- visit v c (slhs x)
    rhs' <- visit v c (srhs x)
    return x { slhs = lhs', srhs = rhs' }

instance (Visitable (c a)) => Visitable (GInfo c a) where
  visit v c x = do
    cm' <- mapM (visit v c) (cm x)
    bs' <- visit v c (bs x)
    return x { cm = cm', bs = bs' }
---------------------------------------------------------------------------------

visitExpr :: (Monoid a) => Visitor a ctx -> ctx -> Expr -> VisitM a Expr
visitExpr v = vE
  where
    vE c e = do {-# SCC "visitExpr.vE.accum" #-} accum acc
                {-# SCC "visitExpr.vE.step" #-} step c' e'
      where c'  = ctxExpr v c e
            e'  = txExpr v c' e
            acc = accExpr v c' e
    step _ e@(ESym _)      = return e
    step _ e@(ECon _)      = return e
    step _ e@(EVar _)      = return e
    step c (EApp f e)      = EApp       <$> vE c f  <*> vE c e
    step c (ENeg e)        = ENeg       <$> vE c e
    step c (EBin o e1 e2)  = EBin o     <$> vE c e1 <*> vE c e2
    step c (EIte p e1 e2)  = EIte       <$> vE c p  <*> vE c e1 <*> vE c e2
    step c (ECst e t)      = (`ECst` t) <$> vE c e
    step c (PAnd  ps)      = PAnd       <$> (vE c <$$> ps)
    step c (POr  ps)       = POr        <$> (vE c <$$> ps)
    step c (PNot p)        = PNot       <$> vE c p
    step c (PImp p1 p2)    = PImp       <$> vE c p1 <*> vE c p2
    step c (PIff p1 p2)    = PIff       <$> vE c p1 <*> vE c p2
    step c (PAtom r e1 e2) = PAtom r    <$> vE c e1 <*> vE c e2
    step c (PAll xts p)    = PAll   xts <$> vE c p
    step c (ELam (x,t) e)  = ELam (x,t) <$> vE c e
    step c (PExist xts p)  = PExist xts <$> vE c p
    step c (ETApp e s)     = (`ETApp` s) <$> vE c e
    step c (ETAbs e s)     = (`ETAbs` s) <$> vE c e
    step _ p@(PKVar _ _)   = return p
    step _ PGrad           = return PGrad

mapKVars :: Visitable t => (KVar -> Maybe Expr) -> t -> t
mapKVars f = mapKVars' f'
  where
    f' (kv', _) = f kv'

mapKVars' :: Visitable t => ((KVar, Subst) -> Maybe Expr) -> t -> t
mapKVars' f            = trans kvVis () []
  where
    kvVis              = defaultVisitor { txExpr = txK }
    txK _ (PKVar k su)
      | Just p' <- f (k, su) = subst su p'
    txK _ p            = p

mapExpr :: (Expr -> Expr) -> Expr -> Expr
mapExpr f = trans (defaultVisitor {txExpr = const f}) () []


mapMExpr :: (Monad m) => (Expr -> m Expr) -> Expr -> m Expr
mapMExpr f = go
  where
    go e@(ESym _)      = f e
    go e@(ECon _)      = f e
    go e@(EVar _)      = f e
    go (EApp g e)      = (EApp       <$> go g  <*> go e) >>= f
    go (ENeg e)        = (ENeg       <$> go e) >>= f
    go (EBin o e1 e2)  = (EBin o     <$> go e1 <*> go e2) >>= f
    go (EIte p e1 e2)  = (EIte       <$> go p  <*> go e1 <*> go e2) >>= f
    go (ECst e t)      = ((`ECst` t) <$> go e) >>= f
    go (PAnd  ps)      = (PAnd       <$> (go <$$> ps)) >>= f
    go (POr  ps)       = (POr        <$> (go <$$> ps)) >>= f
    go (PNot p)        = (PNot       <$> go p) >>= f
    go (PImp p1 p2)    = (PImp       <$> go p1 <*> go p2) >>= f
    go (PIff p1 p2)    = (PIff       <$> go p1 <*> go p2) >>= f
    go (PAtom r e1 e2) = (PAtom r    <$> go e1 <*> go e2) >>= f
    go (PAll xts p)    = (PAll   xts <$> go p) >>= f
    go (ELam (x,t) e)  = (ELam (x,t) <$> go e) >>= f
    go (PExist xts p)  = (PExist xts <$> go p) >>= f
    go (ETApp e s)     = ((`ETApp` s) <$> go e) >>= f
    go (ETAbs e s)     = ((`ETAbs` s) <$> go e) >>= f
    go p@(PKVar _ _)   = f p
    go PGrad           = f PGrad



mapKVarSubsts :: Visitable t => (KVar -> Subst -> Subst) -> t -> t
mapKVarSubsts f        = trans kvVis () []
  where
    kvVis              = defaultVisitor { txExpr = txK }
    txK _ (PKVar k su) = PKVar k $ f k su
    txK _ p            = p

newtype MInt = MInt Integer

instance Monoid MInt where
  mempty                    = MInt 0
  mappend (MInt m) (MInt n) = MInt (m + n)

size :: Visitable t => t -> Integer
size t    = n
  where
    MInt n = fold szV () mempty t
    szV    = (defaultVisitor :: Visitor MInt t) { accExpr = \ _ _ -> MInt 1 }


lamSize :: Visitable t => t -> Integer
lamSize t    = n
  where
    MInt n = fold szV () mempty t
    szV    = (defaultVisitor :: Visitor MInt t) { accExpr = accum }
    accum _ (ELam _ _) = MInt 1
    accum _ _          = MInt 0


kvars :: Visitable t => t -> [KVar]
kvars                 = fold kvVis () []
  where
    kvVis             = (defaultVisitor :: Visitor [KVar] t) { accExpr = kv' }
    kv' _ (PKVar k _) = [k]
    kv' _ _           = []

envKVars :: (TaggedC c a) => BindEnv -> c a -> [KVar]
envKVars be c = squish [ kvs sr |  (_, sr) <- clhs be c]
  where
    squish    = S.toList  . S.fromList . concat
    kvs       = kvars . sr_reft

envKVarsN :: (TaggedC c a) => BindEnv -> c a -> [(KVar, Int)]
envKVarsN be c = tally [ kvs sr |  (_, sr) <- clhs be c]
  where
    tally      = count . concat
    kvs        = kvars . sr_reft

rhsKVars :: (TaggedC c a) => c a -> [KVar]
rhsKVars = kvars . crhs -- rhsCs

isKvarC :: (TaggedC c a) => c a -> Bool
isKvarC = all isKvar . conjuncts . crhs

isConcC :: (TaggedC c a) => c a -> Bool
isConcC = all isConc . conjuncts . crhs

isKvar :: Expr -> Bool
isKvar (PKVar {}) = True
isKvar _          = False

isConc :: Expr -> Bool
isConc = null . kvars

---------------------------------------------------------------------------------
-- | Visitors over @Sort@
---------------------------------------------------------------------------------
foldSort :: (a -> Sort -> a) -> a -> Sort -> a
foldSort f = step
  where
    step b t           = go (f b t) t
    go b (FFunc t1 t2) = L.foldl' step b [t1, t2]
    go b (FApp t1 t2)  = L.foldl' step b [t1, t2]
    go b (FAbs _ t)    = go b t
    go b _             = b

mapSort :: (Sort -> Sort) -> Sort -> Sort
mapSort f = step
  where
    step             = go . f
    go (FFunc t1 t2) = FFunc (step t1) (step t2)
    go (FApp t1 t2)  = FApp (step t1) (step t2)
    go (FAbs i t)    = FAbs i (step t)
    go t             = t

---------------------------------------------------------------
-- | String Constants -----------------------------------------
---------------------------------------------------------------

-- symConstLits    :: FInfo a -> [(Symbol, Sort)]
-- symConstLits fi = [(symbol c, strSort) | c <- symConsts fi]

class SymConsts a where
  symConsts :: a -> [SymConst]

instance  SymConsts (FInfo a) where
  symConsts fi = sortNub $ csLits ++ bsLits ++ qsLits
    where
      csLits   = concatMap symConsts $ M.elems  $  cm    fi
      bsLits   = symConsts           $ bs                fi
      qsLits   = concatMap symConsts $ qBody  <$> quals fi

instance SymConsts BindEnv where
  symConsts    = concatMap (symConsts . snd) . M.elems . beBinds

instance SymConsts (SubC a) where
  symConsts c  = symConsts (slhs c) ++
                 symConsts (srhs c)

instance SymConsts SortedReft where
  symConsts = symConsts . sr_reft

instance SymConsts Reft where
  symConsts (Reft (_, ra)) = getSymConsts ra


instance SymConsts Expr where
  symConsts = getSymConsts

getSymConsts :: Visitable t => t -> [SymConst]
getSymConsts         = fold scVis () []
  where
    scVis            = (defaultVisitor :: Visitor [SymConst] t)  { accExpr = sc }
    sc _ (ESym c)    = [c]
    sc _ _           = []
