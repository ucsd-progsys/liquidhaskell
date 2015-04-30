{-# LANGUAGE TupleSections #-}

module Language.Fixpoint.Visitor (
  -- * Visitor
     Visitor (..)

  -- * Default Visitor
  , defaultVisitor

  -- * Transformers
  , trans

  -- * Accumulators
  , fold

  -- * Clients
  , kvars
  , envKVars
  , mapKVars

  -- * Sorts
  , foldSort, mapSort
  ) where

import           Control.Applicative       (Applicative, (<$>), (<*>))
import           Control.Monad.Trans.State (State, modify, runState)
import           Data.Monoid
import           Data.Traversable          (Traversable, traverse)
import           Language.Fixpoint.Types
import qualified Data.HashSet as S
import qualified Data.List    as L

data Visitor acc ctx = Visitor {
 -- | Context @ctx@ is built in a "top-down" fashion; not "across" siblings
    ctxExpr :: ctx -> Expr -> ctx
  , ctxPred :: ctx -> Pred -> ctx

  -- | Transforms can access current @ctx@
  , txExpr  :: ctx -> Expr -> Expr
  , txPred  :: ctx -> Pred -> Pred

  -- | Accumulations can access current @ctx@; @acc@ value is monoidal
  , accExpr :: ctx -> Expr -> acc
  , accPred :: ctx -> Pred -> acc
  }

---------------------------------------------------------------------------------
defaultVisitor :: Monoid acc => Visitor acc ctx
---------------------------------------------------------------------------------
defaultVisitor = Visitor {
    ctxExpr    = \c _ -> c
  , ctxPred    = \c _ -> c
  , txExpr     = \_ x -> x
  , txPred     = \_ x -> x
  , accExpr    = \_ _ -> mempty
  , accPred    = \_ _ -> mempty
  }

------------------------------------------------------------------------

fold         :: (Visitable t, Monoid a) => Visitor a ctx -> ctx -> a -> t -> a
fold v c a t = snd $ execVisitM v c a visit t

trans        :: (Visitable t, Monoid a) => Visitor a ctx -> ctx -> a -> t -> t
trans v c a z = fst $ execVisitM v c mempty visit z

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

instance Visitable Pred where
  visit = visitPred

instance Visitable Refa where
  visit v c (Refa p) =  Refa <$> visit v c p
  visit _ _ r        = return r

instance Visitable Reft where
  visit v c (Reft (x, ra)) = (Reft . (x, )) <$> visit v c ra

visitMany :: (Monoid a, Visitable t) => Visitor a ctx -> ctx -> [t] -> VisitM a [t]
visitMany v c xs = visit v c <$$> xs

visitExpr :: (Monoid a) => Visitor a ctx -> ctx -> Expr -> VisitM a Expr
visitExpr v = vE
  where
    vP     = visitPred v
    vE c e = accum acc >> step c' e' where c'  = ctxExpr v c e
                                           e'  = txExpr v c' e
                                           acc = accExpr v c' e
    step _ e@EBot         = return e
    step _ e@(ESym _)     = return e
    step _ e@(ECon _)     = return e
    step _ e@(ELit _ _)   = return e
    step _ e@(EVar _)     = return e
    step c (EApp f es)    = EApp f     <$> (vE c <$$> es)
    step c (ENeg e)       = ENeg       <$> vE c e
    step c (EBin o e1 e2) = EBin o     <$> vE c e1 <*> vE c e2
    step c (EIte p e1 e2) = EIte       <$> vP c p  <*> vE c e1 <*> vE c e2
    step c (ECst e t)     = (`ECst` t) <$> vE c e

visitPred :: (Monoid a) => Visitor a ctx -> ctx -> Pred -> VisitM a Pred
visitPred v = vP
  where
    -- vS1 c (x, e)  = (x,) <$> vE c e
    -- vS c (Su xes) = Su <$> vS1 c <$$> xes
    vE      = visitExpr v
    vP c p  = accum acc >> step c' p' where c'   = ctxPred v c p
                                            p'   = txPred v c' p
                                            acc  = accPred v c' p
    step c (PAnd  ps)      = PAnd     <$> (vP c <$$> ps)
    step c (POr  ps)       = POr      <$> (vP c <$$> ps)
    step c (PNot p)        = PNot     <$> vP c p
    step c (PImp p1 p2)    = PImp     <$> vP c p1 <*> vP c p2
    step c (PIff p1 p2)    = PIff     <$> vP c p1 <*> vP c p2
    step c (PBexp  e)      = PBexp    <$> vE c e
    step c (PAtom r e1 e2) = PAtom r  <$> vE c e1 <*> vE c e2
    step c (PAll xts p)    = PAll xts <$> vP c p
    step c (PExist x p)    = PExist x <$> vP c p
    step _ p@(PKVar _ _)   = return p -- PAtom r  <$> vE c e1 <*> vE c e2
    step _ p@PTrue         = return p
    step _ p@PFalse        = return p
    step _ p@PTop          = return p


---------------------------------------------------------------------------------
-- reftKVars :: Reft -> [KVar]
---------------------------------------------------------------------------------

-- reftKVars (Reft (_, ra)) = predKVars $ raPred ra
-- predKVars            :: Pred -> [Symbol]

mapKVars :: Visitable t => (KVar -> Maybe Pred) -> t -> t
mapKVars f             = trans kvVis () []
  where
    kvVis              = defaultVisitor { txPred = txK }
    txK _ (PKVar k su)
      | Just p' <- f k = subst su p'
    txK _ p            = p

kvars :: Visitable t => t -> [KVar]
kvars                = fold kvVis () []
  where
    kvVis            = defaultVisitor { accPred = kv }
    kv _ (PKVar k _) = [k]
    kv _ _           = []

envKVars :: BindEnv -> SubC a -> [KVar]
envKVars be c = squish [ kvs sr |  (_, sr) <- envCs be (senv c)]
  where
    squish = S.toList  . S.fromList . concat
    kvs    = kvars . sr_reft



---------------------------------------------------------------------------------
-- | Visitors over @Sort@
---------------------------------------------------------------------------------
foldSort :: (a -> Sort -> a) -> a -> Sort -> a
---------------------------------------------------------------------------------
foldSort f = step
  where
    step b t          = go (f b t) t
    go b (FFunc _ ts) = L.foldl' step b ts
    go b (FApp _ ts)  = L.foldl' step b ts
    go b _            = b


---------------------------------------------------------------------------------
mapSort :: (Sort -> Sort) -> Sort -> Sort
---------------------------------------------------------------------------------
mapSort f = step
  where
    step            = go . f
    go (FFunc n ts) = FFunc n $ step <$> ts
    go (FApp c ts)  = FApp c  $ step <$> ts
    go t            = t
