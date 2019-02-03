
-------------------------------------------------------------------------------
-- | This module formalizes the key datatypes needed to represent Horn NNF 
--   constraints as described in "Local Refinement Typing", ICFP 2017
-------------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}

module Language.Fixpoint.Horn.Types 
  ( -- * Horn Constraints and their components
    Query (..)
  , Cstr  (..)
  , Pred  (..)
  , Bind  (..)
  , Var   (..) 

    -- * invariants (refinements) on constraints 
  , okCstr 
  , dummyBind
  ) 
  where 

import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import qualified Language.Fixpoint.Types as F

-------------------------------------------------------------------------------
-- | @HVar@ is a Horn variable 
-------------------------------------------------------------------------------
data Var a = HVar
  { hvName :: !F.Symbol                         -- ^ name of the variable $k1, $k2 etc.
  , hvArgs :: ![F.Sort] {- len hvArgs > 0 -}    -- ^ sorts of its parameters i.e. of the relation defined by the @HVar@
  , hvMeta :: a                                 -- ^ meta-data
  }
  deriving (Eq, Ord, Data, Typeable, Generic, Functor)

-------------------------------------------------------------------------------
-- | @HPred@ is a Horn predicate that appears as LHS (body) or RHS (head) of constraints 
-------------------------------------------------------------------------------
data Pred 
  = Reft  !F.Expr                               -- ^ r 
  | Var   !F.Symbol ![F.Symbol]                 -- ^ $k(y1..yn) 
  | PAnd  ![Pred]                               -- ^ p1 /\ .../\ pn 
  deriving (Data, Typeable, Generic)
   
-------------------------------------------------------------------------------
-- | @Cst@ is an NNF Horn Constraint. 
-------------------------------------------------------------------------------
-- Note that a @Bind@ is a simplified @F.SortedReft@ ...
data Bind = Bind 
  { bSym  :: !F.Symbol 
  , bSort :: !F.Sort 
  , bPred :: !Pred 
  }
  deriving (Data, Typeable, Generic)

dummyBind :: Bind 
dummyBind = Bind F.dummySymbol F.intSort (PAnd []) 

data Cstr a
  = Head  !Pred a               -- ^ p
  | CAnd  ![(Cstr a)]           -- ^ c1 /\ ... /\ cn
  | All   !Bind  !(Cstr a)      -- ^ \all x:t. p => c
  | Any   !Bind  !(Cstr a)      -- ^ \exi x:t. p => c
  deriving (Data, Typeable, Generic, Functor)

-- We want all valid constraints to start with a binding at the top
okCstr :: Cstr a -> Bool 
okCstr (All {}) = True 
okCstr (Any {}) = True 
okCstr _        = False 

-------------------------------------------------------------------------------
-- | @Query@ is an NNF Horn Constraint. 
-------------------------------------------------------------------------------

data Query a = Query 
  { qQuals :: ![F.Qualifier]                    -- ^ qualifiers over which to solve cstrs
  , qVars  :: ![Var a]                          -- ^ kvars, with parameter-sorts
  , qCstr  :: !(Cstr a)                         -- ^ list of constraints
  }
  deriving (Data, Typeable, Generic, Functor)
