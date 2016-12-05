{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DeriveGeneric              #-}

-- | This module contains the top-level SOLUTION data types,
--   including various indices used for solving.

module Language.Fixpoint.Types.Solutions (

  -- * Solution tables
    Solution
  , Sol
  , sScp
  , CMap

  -- * Solution elements
  , Hyp, Cube (..), QBind

  -- * Solution Candidates (move to SolverMonad?)
  , Cand

  -- * Constructor
  , fromList

  -- * Update
  , updateK

  -- * Lookup
  , lookupQBind
  , lookup
  , qBindPred

  -- * Conversion for client
  , result

  -- * "Fast" Solver (DEPRECATED as unsound)
  , Index  (..)
  , KIndex (..)
  , BindPred (..)
  , BIndex (..)
  ) where

import           Prelude hiding (lookup)
import           GHC.Generics
import           Data.Hashable
import qualified Data.HashMap.Strict       as M
-- import qualified Data.HashSet              as S
import           Language.Fixpoint.Misc

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Text.PrettyPrint.HughesPJ

--------------------------------------------------------------------------------
-- | The `Solution` data type --------------------------------------------------
--------------------------------------------------------------------------------
type Solution = Sol QBind
type QBind    = [EQual]

--------------------------------------------------------------------------------
-- | A `Sol` contains the various indices needed to compute a solution,
--   in particular, to compute `lhsPred` for any given constraint.
--------------------------------------------------------------------------------
data Sol a = Sol
  { sMap  :: !(M.HashMap KVar a)         -- ^ actual solution (for cut kvar)
  , sHyp  :: !(M.HashMap KVar Hyp)       -- ^ defining cubes  (for non-cut kvar)
  -- , sBot  :: !(M.HashMap KVar ())        -- ^ set of BOT (cut kvars)
  , sScp  :: !(M.HashMap KVar IBindEnv)  -- ^ set of allowed binders for kvar
  }

instance Monoid (Sol a) where
  mempty        = Sol mempty mempty mempty
  mappend s1 s2 = Sol { sMap  = mappend (sMap s1) (sMap s2)
                      , sHyp  = mappend (sHyp s1) (sHyp s2)
    --                , sBot  = mappend (sBot s1) (sBot s2)
                      , sScp  = mappend (sScp s1) (sScp s2)
                      }

instance Functor Sol where
  fmap f (Sol s m1 m2) = Sol (f <$> s) m1 m2

instance PPrint a => PPrint (Sol a) where
  pprintTidy k = pprintTidy k . sMap


--------------------------------------------------------------------------------
-- | A `Cube` is a single constraint defining a KVar ---------------------------
--------------------------------------------------------------------------------
type Hyp      = ListNE Cube

data Cube = Cube
  { cuBinds :: IBindEnv  -- ^ Binders       from defining Env
  , cuSubst :: Subst     -- ^ Substitutions from cstrs    Rhs
  , cuId    :: SubcId    -- ^ Id            of   defining Cstr
  , cuTag   :: Tag       -- ^ Tag           of   defining Cstr (DEBUG)
  }

instance PPrint Cube where
  pprintTidy _ c = "Cube" <+> pprint (cuId c)

--------------------------------------------------------------------------------
result :: Solution -> M.HashMap KVar Expr
--------------------------------------------------------------------------------
result s = sMap $ (pAnd . fmap eqPred) <$> s

--------------------------------------------------------------------------------
-- | Create a Solution ---------------------------------------------------------
--------------------------------------------------------------------------------
fromList :: [(KVar, a)] -> [(KVar, Hyp)] -> M.HashMap KVar IBindEnv -> Sol a
fromList kXs kYs = Sol kXm kYm -- kBm
  where
    kXm          = M.fromList   kXs
    kYm          = M.fromList   kYs
 -- kBm          = const () <$> kXm
--------------------------------------------------------------------------------
qBindPred :: Subst -> QBind -> Pred
--------------------------------------------------------------------------------
qBindPred su = subst su . pAnd . fmap eqPred

--------------------------------------------------------------------------------
-- | Read / Write Solution at KVar ---------------------------------------------
--------------------------------------------------------------------------------
lookupQBind :: Solution -> KVar -> QBind
--------------------------------------------------------------------------------
lookupQBind s k = {- tracepp ("lookupQB: k = " ++ show k) $ -} M.lookupDefault [] k (sMap s)

--------------------------------------------------------------------------------
lookup :: Solution -> KVar -> Either Hyp QBind
--------------------------------------------------------------------------------
-- lookup s k =
  -- case M.lookup k (sHyp s) of
    -- Just cs -> Left cs
    -- Nothing -> if M.member k (sBot s)
                -- then Left []
                -- else case M.lookup (tracepp "AHA k is not in BOT" k) (sMap s) of
                       -- Just eqs -> Right eqs
                       -- Nothing  -> errorstar $ "solLookup: Unknown kvar " ++ show k

lookup s k
  | Just cs  <- M.lookup k (sHyp s)               -- non-cut variable, return its cubes
  = Left cs
  | Just eqs <- M.lookup k (sMap s)
  = Right eqs                                     -- TODO: don't initialize kvars that have a hyp solution
  | otherwise
  = errorstar $ "solLookup: Unknown kvar " ++ show k

--------------------------------------------------------------------------------
updateK :: KVar -> a -> Sol a -> Sol a
--------------------------------------------------------------------------------
updateK k qs s = s { sMap = M.insert k qs (sMap s)
--                 , sBot = M.delete k    (sBot s)
                   }


--------------------------------------------------------------------------------
-- | A `Cand` is an association list indexed by predicates
--------------------------------------------------------------------------------
type Cand a   = [(Expr, a)]


--------------------------------------------------------------------------------
-- | A KIndex uniquely identifies each *use* of a KVar in an (LHS) binder
--------------------------------------------------------------------------------
data KIndex = KIndex { kiBIndex :: !BindId
                     , kiPos    :: !Int
                     , kiKVar   :: !KVar
                     }
              deriving (Eq, Ord, Show, Generic)

instance Hashable KIndex

instance PPrint KIndex where
  pprintTidy _ = tshow

--------------------------------------------------------------------------------
-- | A BIndex is created for each LHS Bind or RHS constraint
--------------------------------------------------------------------------------
data BIndex    = Root
               | Bind !BindId
               | Cstr !SubcId
                 deriving (Eq, Ord, Show, Generic)

instance Hashable BIndex

instance PPrint BIndex where
  pprintTidy _ = tshow

--------------------------------------------------------------------------------
-- | Each `Bind` corresponds to a conjunction of a `bpConc` and `bpKVars`
--------------------------------------------------------------------------------
data BindPred  = BP
  { bpConc :: !Pred                  -- ^ Concrete predicate (PTrue o)
  , bpKVar :: ![KIndex]              -- ^ KVar-Subst pairs
  } deriving (Show)

instance PPrint BindPred where
  pprintTidy _ = tshow


--------------------------------------------------------------------------------
-- | A Index is a suitably indexed version of the cosntraints that lets us
--   1. CREATE a monolithic "background formula" representing all constraints,
--   2. ASSERT each lhs via bits for the subc-id and formulas for dependent cut KVars
--------------------------------------------------------------------------------
data Index = FastIdx
  { bindExpr   :: !(BindId |-> BindPred) -- ^ BindPred for each BindId
  , kvUse      :: !(KIndex |-> KVSub)    -- ^ Definition of each `KIndex`
  , kvDef      :: !(KVar   |-> Hyp)      -- ^ Constraints defining each `KVar`
  , envBinds   :: !(CMap IBindEnv)       -- ^ Binders of each Subc
  , envTx      :: !(CMap [SubcId])       -- ^ Transitive closure oof all dependent binders
  , envSorts   :: !(SEnv Sort)           -- ^ Sorts for all symbols
  -- , bindPrev   :: !(BIndex |-> BIndex)   -- ^ "parent" (immediately dominating) binder
  -- , kvDeps     :: !(CMap [KIndex])       -- ^ List of (Cut) KVars on which a SubC depends
  }

type CMap a  = M.HashMap SubcId a
