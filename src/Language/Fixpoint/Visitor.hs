module Language.Fixpoint.Visitor (

  -- * Transformers
    trans
            
  -- * Accumulators
  , fold

  ) where

import           Data.Monoid
import           Data.Traversable               (traverse)
import           Control.Applicative            (Applicative (), (<$>), (<*>))
import           Control.Exception              (throw)
import           Control.Monad.Trans.State      (modify, State, runState)
import           Language.Fixpoint.Misc         (mapSnd)
import           Language.Fixpoint.Types



data Visitor acc ctx = Visitor {
 -- | Context @ctx@ is built up in a "top-down" fashion but not across siblings
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

trans        :: (Visitable t, Monoid a) => Visitor a ctx -> ctx -> t -> t 
trans v c z  = fst $ execVisitM v c mempty visit z 

execVisitM v c a f x = runState (f v c x) a

type VisitM acc = State acc 

accum :: (Monoid a) => a -> VisitM a ()
accum = modify . mappend

f <$$> x = traverse f x

------------------------------------------------------------------------------
class Visitable t where
  visit :: (Monoid a) => Visitor a c -> c -> t -> VisitM a t

instance Visitable Expr where
  visit = visitExpr

instance Visitable Pred where
  visit = visitPred

visitExpr :: (Monoid a) => Visitor a ctx -> ctx -> Expr -> VisitM a Expr 
visitExpr v = vE
  where
    vP      = visitPred v
    vE c e  = accum acc >> step c' e' where c'  = ctxExpr v c e
                                            e'  = txExpr v c' e
                                            acc = accExpr v c' e
    step c e@EBot         = return e
    step c e@(ESym _)     = return e   
    step c e@(ECon _)     = return e 
    step c e@(ELit _ _)   = return e 
    step c e@(EVar _)     = return e
    step c (EApp f es)    = EApp f     <$> (vE c <$$> es)  
    step c (EBin o e1 e2) = EBin o     <$> vE c e1 <*> vE c e2
    step c (EIte p e1 e2) = EIte       <$> vP c p  <*> vE c e1 <*> vE c e2
    step c (ECst e t)     = (`ECst` t) <$> vE c e
 
visitPred :: (Monoid a) => Visitor a ctx -> ctx -> Pred -> VisitM a Pred 
visitPred v = vP
  where
    vE     = visitExpr v
    vP c p = accum acc >> step c' p' where c'   = ctxPred v c p
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
    step c p@PTrue         = return p
    step c p@PFalse        = return p
    step c p@PTop          = return p
    
