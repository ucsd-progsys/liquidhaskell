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
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TupleSections              #-}

-- | This module contains the top-level SOLUTION data types,
--   including various indices used for solving.

module Language.Fixpoint.Types.Solutions (

  -- * Solution tables
    Solution
  , Sol, sEnv
  , sScp
  , CMap

  -- * Solution elements
  , Hyp, Cube (..), QBind
  , EQual (..)
  , eQual

  -- * Solution Candidates (move to SolverMonad?)
  , Cand

  -- * Constructor
  , fromList

  -- * Update
  , update

  -- * Lookup
  , lookupQBind
  , lookup

  -- * Manipulating QBind
  , qb
  , qbPreds
  , qbFilter

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
import           Control.DeepSeq
import           Data.Maybe (fromMaybe)
import           Data.Hashable
import qualified Data.HashMap.Strict       as M
import qualified Data.List as L
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
-- import qualified Data.HashSet              as S
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.SortCheck (elaborate)
import           Text.PrettyPrint.HughesPJ

--------------------------------------------------------------------------------
-- | Update Solution -----------------------------------------------------------
--------------------------------------------------------------------------------
update :: Solution -> [KVar] -> [(KVar, EQual)] -> (Bool, Solution)
--------------------------------------------------------------------------------
update s ks kqs = {- tracepp msg -} (or bs, s')
  where
    kqss        = groupKs ks kqs
    (bs, s')    = folds update1 s kqss
    -- msg      = printf "ks = %s, s = %s" (showpp ks) (showpp s)

folds   :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
folds f b = L.foldl' step ([], b)
  where
     step (cs, acc) x = (c:cs, x')
       where
         (c, x')      = f acc x

groupKs :: [KVar] -> [(KVar, EQual)] -> [(KVar, QBind)]
groupKs ks kqs = [ (k, QB eqs) | (k, eqs) <- M.toList $ groupBase m0 kqs ]
  where
    m0         = M.fromList $ (,[]) <$> ks

update1 :: Solution -> (KVar, QBind) -> (Bool, Solution)
update1 s (k, qs) = (change, updateK k qs s)
  where
    oldQs         = lookupQBind s k
    change        = qbSize oldQs /= qbSize qs

--------------------------------------------------------------------------------
-- | The `Solution` data type --------------------------------------------------
--------------------------------------------------------------------------------
type Solution = Sol QBind
newtype QBind = QB [EQual] deriving (Show, Data, Typeable, Generic)

qb :: [EQual] -> QBind
qb = QB

qbEQuals :: QBind -> [EQual]
qbEQuals (QB xs) = xs

qbSize :: QBind -> Int
qbSize = length . qbEQuals

qbFilter :: (EQual -> Bool) -> QBind -> QBind
qbFilter f (QB eqs) = QB (filter f eqs)

instance NFData QBind

instance PPrint QBind where
  pprintTidy k = pprintTidy k . qbEQuals

--------------------------------------------------------------------------------
-- | A `Sol` contains the various indices needed to compute a solution,
--   in particular, to compute `lhsPred` for any given constraint.
--------------------------------------------------------------------------------
data Sol a = Sol
  { sEnv  :: !(SEnv Sort)                -- ^ Environment used to elaborate solutions
  , sMap  :: !(M.HashMap KVar a)         -- ^ Actual solution (for cut kvar)
  , sHyp  :: !(M.HashMap KVar Hyp)       -- ^ Defining cubes  (for non-cut kvar)
  -- , sBot  :: !(M.HashMap KVar ())        -- ^ set of BOT (cut kvars)
  , sScp  :: !(M.HashMap KVar IBindEnv)  -- ^ set of allowed binders for kvar
  }

instance Monoid (Sol a) where
  mempty        = Sol mempty mempty mempty mempty
  mappend s1 s2 = Sol { sEnv  = mappend (sEnv s1) (sEnv s2)
                      , sMap  = mappend (sMap s1) (sMap s2)
                      , sHyp  = mappend (sHyp s1) (sHyp s2)
    --                , sBot  = mappend (sBot s1) (sBot s2)
                      , sScp  = mappend (sScp s1) (sScp s2)
                      }

instance Functor Sol where
  fmap f (Sol e s m1 m2) = Sol e (f <$> s) m1 m2

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
result s = sMap $ (pAnd . fmap eqPred . qbEQuals) <$> s

--------------------------------------------------------------------------------
-- | Create a Solution ---------------------------------------------------------
--------------------------------------------------------------------------------
fromList :: SEnv Sort -> [(KVar, a)] -> [(KVar, Hyp)] -> M.HashMap KVar IBindEnv -> Sol a
fromList env kXs kYs = Sol env kXm kYm -- kBm
  where
    kXm              = M.fromList   kXs
    kYm              = M.fromList   kYs
 -- kBm              = const () <$> kXm

--------------------------------------------------------------------------------
qbPreds :: String -> Solution -> Subst -> QBind -> [(Pred, EQual)]
--------------------------------------------------------------------------------
qbPreds msg s su (QB eqs) = [ (elabPred eq, eq) | eq <- eqs ]
  where
    elabPred          = elaborate ("qbPreds:" ++ msg) env . subst su . eqPred
    env               = sEnv s

--------------------------------------------------------------------------------
-- | Read / Write Solution at KVar ---------------------------------------------
--------------------------------------------------------------------------------
lookupQBind :: Solution -> KVar -> QBind
--------------------------------------------------------------------------------
lookupQBind s k = {- tracepp _msg $ -} fromMaybe (QB []) (lookupElab s k)
  where
    _msg        = "lookupQB: k = " ++ show k

--------------------------------------------------------------------------------
lookup :: Solution -> KVar -> Either Hyp QBind
--------------------------------------------------------------------------------
lookup s k
  | Just cs  <- M.lookup k (sHyp s) -- non-cut variable, return its cubes
  = Left cs
  | Just eqs <- lookupElab s k
  = Right eqs                       -- TODO: don't initialize kvars that have a hyp solution
  | otherwise
  = errorstar $ "solLookup: Unknown kvar " ++ show k

lookupElab :: Solution -> KVar -> Maybe QBind
lookupElab s k = M.lookup k (sMap s)

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
-- | Instantiated Qualifiers ---------------------------------------------------
--------------------------------------------------------------------------------
data EQual = EQL
  { _eqQual :: !Qualifier
  , eqPred  :: !Expr
  , _eqArgs :: ![Expr]
  } deriving (Eq, Show, Data, Typeable, Generic)

instance PPrint EQual where
  pprintTidy k = pprintTidy k . eqPred

instance NFData EQual

{- EQL :: q:_ -> p:_ -> ListX F.Expr {q_params q} -> _ @-}
eQual :: Qualifier -> [Symbol] -> EQual
eQual q xs = {- tracepp "eQual" $ -} EQL q p es
  where
    p      = subst su $  qBody q
    su     = mkSubst  $  safeZip "eQual" qxs es
    es     = eVar    <$> xs
    qxs    = fst     <$> qParams q

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
