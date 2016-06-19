{-# LANGUAGE TypeSynonymInstances #-}

module Prover.Types where

import Prover.Constants (default_depth)

import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Types hiding (Predicate, EApp, EVar, Expr)

type LVar     = Var     ()
type LVarCtor = VarCtor ()
type LAxiom   = Axiom   ()
type LQuery   = Query   ()


data Axiom a = Axiom { axiom_name :: Var a
                     , axiom_vars :: [LVar]
                     , axiom_body :: Predicate
                     }

data Var a   = Var { var_name :: Symbol
                   , var_sort :: Sort
                   , var_info :: a
                   }

instance Eq (Var a) where
  v1 == v2 = (var_name v1) == (var_name v2)


-- Note: Ctors may be higher order, like compose
-- when not fully instantiated, the predicate should not be used
data Ctor a  = Ctor { ctor_expr :: Expr a
                    , ctor_sort :: Sort
                    , ctor_vars :: [LVar]
                    , ctor_prop :: Predicate
                    }
              -- constructors can be expressions like (compose f g)


data VarCtor a  = VarCtor { vctor_var  :: Var a
                          , vctor_vars :: [LVar]
                          , vctor_prop :: Predicate
                          }


instance Eq (Ctor a) where
  c1 == c2 = (ctor_expr c1) == (ctor_expr c2)

data Expr a  = EVar (Var a)
             | EApp (Ctor a) [Expr a]

  deriving (Eq)

newtype Predicate = Pred {p_pred :: F.Expr}

data Proof a     = Invalid
                 | Proof { p_evidence :: [Instance a]}

data Instance a  = Inst { inst_axiom :: Axiom a
                        , inst_args  :: [Expr a]
                        , inst_pred  :: Predicate
                        }


data Query a = Query { q_axioms :: ![Axiom a]
                     , q_ctors  :: ![VarCtor a]
                     , q_vars   :: ![Var a]
                     , q_env    :: ![LVar]
                     , q_goal   :: !Predicate
                     , q_fname  :: !FilePath
                     , q_depth  :: !Int
                     , q_decls  :: [Predicate]
                     , q_isHO   :: Bool
                     }

-- | ArgExpr provides for each sort s
-- | a list of expressions of sort s
-- | and the list of constroctors that can create an expression of sort s.
data ArgExpr a = ArgExpr { arg_sort  :: Sort
                         , arg_exprs :: [Expr a]
                         , arg_ctors :: [Ctor a]
                         }

instance Monoid Predicate where
    mempty                      = Pred mempty
    mappend (Pred p1) (Pred p2) = Pred (p1 `mappend` p2)

instance Monoid (Query a) where
    mempty        = Query { q_axioms = mempty
                          , q_ctors  = mempty
                          , q_vars   = mempty
                          , q_env    = mempty
                          , q_goal   = mempty
                          , q_fname  = mempty
                          , q_depth  = default_depth
                          , q_decls  = mempty
                          , q_isHO   = False
                          }
    mappend q1 q2 = Query { q_axioms = q_axioms q1 `mappend` q_axioms q2
                          , q_ctors  = q_ctors  q1 `mappend` q_ctors  q2
                          , q_env    = q_env    q1 `mappend` q_env    q2
                          , q_vars   = q_vars   q1 `mappend` q_vars   q2
                          , q_goal   = q_goal   q1 `mappend` q_goal   q2
                          , q_fname  = q_fname  q1 `mappend` q_fname  q2
                          , q_decls  = q_decls  q1 `mappend` q_decls  q2
                          , q_depth  = q_depth  q1 `max`     q_depth  q2
                          , q_isHO   = q_isHO   q1 ||        q_isHO   q2
                          }


instance F.Subable Predicate where
  subst su (Pred p)  = Pred $ subst su p
  substa su (Pred p) = Pred $ substa su p
  substf su (Pred p) = Pred $ substf su p
  syms (Pred p)      = syms p

varCtorToCtor :: VarCtor a -> Ctor a
varCtorToCtor (VarCtor v vs p) = Ctor (EVar v) (var_sort v) vs p


isEVar :: Expr a -> Bool
isEVar (EVar _) = True
isEVar _        = False

mkExpr :: Expr a -> F.Expr
mkExpr (EVar v)
  = F.EVar (var_name v)
mkExpr (EApp c es)
  = F.eApps (mkExpr $ ctor_expr c) (mkExpr <$> es)
