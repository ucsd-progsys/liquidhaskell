{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}

-- | This module contains the top-level SOLUTION data types,
--   including various indices used for solving.

module Language.Fixpoint.Types.Solutions (

  -- * Solution tables
    Solution
  , Sol

  -- * Solution elements
  , Hyp, Cube (..), QBind

  -- * Solution Candidates (move to SolverMonad?)
  , Cand

  -- * Constructor
  , fromList

  -- * Update
  , insert

  -- * Lookup
  , lookupQBind
  , lookup

  -- * Conversion for client
  , result


  -- * "Fast" Solver
  , Index  (..)
  , KIndex (..)
  , BindPred (..)
  , BIndex
  ) where

import           Prelude hiding (lookup)
import qualified Data.HashMap.Strict       as M

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints

-- import           Text.PrettyPrint.HughesPJ
-- import qualified Data.HashSet              as S

--------------------------------------------------------------------------------
-- | The `Solution` data type --------------------------------------------------
--------------------------------------------------------------------------------

type Solution = Sol QBind
type QBind    = [EQual]



--------------------------------------------------------------------------------
-- | A `Sol` contains the various indices needed to compute a solution,
--   in particular, to compute `lhsPred` for any given constraint.
--------------------------------------------------------------------------------
data Sol a = Sol { sMap  :: !(M.HashMap KVar a)
                 , sHyp  :: !(M.HashMap KVar Hyp)
                 , sIdx  :: !(Maybe Index)
                 }

instance Monoid (Sol a) where
  mempty        = Sol mempty mempty Nothing
  mappend s1 s2 = Sol { sMap  = mappend (sMap s1) (sMap s2)
                      , sHyp  = mappend (sHyp s1) (sHyp s2)
                      , sIdx  = sIdx s1
                      }

instance Functor Sol where
  fmap f (Sol s h z) = Sol (f <$> s) h z

instance PPrint a => PPrint (Sol a) where
  pprintTidy k = pprintTidy k . sMap


--------------------------------------------------------------------------------
-- | A `Cube` is a single constraint defining a KVar ---------------------------
--------------------------------------------------------------------------------
type Hyp      = ListNE Cube

data Cube = Cube
  { cuBinds :: IBindEnv  -- ^ Binders       from defining Env
  , cuSubst :: Subst     -- ^ Substitutions from cstrs    Rhs
  , cuId    :: Integer   -- ^ Id            of   defining Cstr (DEBUG)
  , cuTag   :: Tag       -- ^ Tag           of   defining Cstr (DEBUG)
  }

--------------------------------------------------------------------------------
result :: Solution -> M.HashMap KVar Expr
--------------------------------------------------------------------------------
result s = sMap $ (pAnd . fmap eqPred) <$> s


--------------------------------------------------------------------------------
-- | Create a Solution ---------------------------------------------------------
--------------------------------------------------------------------------------
fromList :: [(KVar, a)] -> [(KVar, Hyp)] -> Maybe Index -> Sol a
fromList kXs kYs = Sol (M.fromList kXs) (M.fromList kYs)

--------------------------------------------------------------------------------
-- | Read / Write Solution at KVar ---------------------------------------------
--------------------------------------------------------------------------------
lookupQBind :: Solution -> KVar -> QBind
--------------------------------------------------------------------------------
lookupQBind s k = M.lookupDefault [] k (sMap s)

--------------------------------------------------------------------------------
lookup :: Solution -> KVar -> Either Hyp QBind
--------------------------------------------------------------------------------
lookup s k
  | Just cs  <- M.lookup k (sHyp s)
  = Left cs
  | Just eqs <- M.lookup k (sMap s)
  = Right eqs -- TODO: don't initialize kvars that have a hyp solution
  | otherwise
  = errorstar $ "solLookup: Unknown kvar " ++ show k

--------------------------------------------------------------------------------
insert :: KVar -> a -> Sol a -> Sol a
-------------------------------------------------------------------------------
insert k qs s = s { sMap = M.insert k qs (sMap s) }


--------------------------------------------------------------------------------
-- | A `Cand` is an association list indexed by predicates
--------------------------------------------------------------------------------
type Cand a   = [(Expr, a)]


--------------------------------------------------------------------------------
-- | A KIndex uniquely identifies each *use* of a KVar in an (LHS) binder
--------------------------------------------------------------------------------
newtype KIndex = KIndex Int

--------------------------------------------------------------------------------
-- | A BIndex is created for each LHS Bind or RHS constraint
--------------------------------------------------------------------------------
data BIndex    = Bind !BindId
               | Cstr !SubcId
                 deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- | Each `Bind` corresponds to a conjunction of a `bpConc` and `bpKVars`
--------------------------------------------------------------------------------
data BindPred  = BP
  { bpConc :: !Pred                   -- ^ Concrete predicate (PTrue o)
  , bpKVar :: [KIndex]                  -- ^ KVar-Subst pairs
  }


--------------------------------------------------------------------------------
-- | A Index is a suitably indexed version of the cosntraints that lets us
--   1. CREATE a monolithic "background formula" representing all constraints,
--   2. ASSERT each lhs via bits for the subc-id and formulas for dependent cut KVars
--------------------------------------------------------------------------------
data Index = FastIdx
  { bindExpr :: BindId |-> BindPred   -- ^ BindPred for each BindId
  , bindPrev :: BindId |-> BindId   -- ^ "parent" (immediately dominating) binder
  , kvUse    :: KIndex |-> KVSub    -- ^ Definition of each `KIndex`
  , kvDef    :: KVar   |-> Hyp    -- ^ Constraints defining each `KVar`
  }
