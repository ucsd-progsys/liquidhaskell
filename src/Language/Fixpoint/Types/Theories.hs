{- LANGUAGE FlexibleInstances         #-}
{- LANGUAGE FlexibleContexts          #-}
{- LANGUAGE NoMonomorphismRestriction #-}
{- LANGUAGE OverloadedStrings         #-}
{- LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Types.Theories (

    -- * Serialized Representation
      Raw

    -- * Theory Symbol
    , TheorySymbol (..)
    , Sem (..)

    -- * Symbol Environments
    , SymEnv (..)
    , symEnv
    , symEnvSort
    , symEnvTheory
    , insertSymEnv

    ) where

import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Environments

import qualified Data.Text.Lazy           as LT

-- import           Language.Fixpoint.Misc   (traceShow)

--------------------------------------------------------------------------------
-- | 'Raw' is the low-level representation for SMT values
--------------------------------------------------------------------------------
type Raw          = LT.Text

--------------------------------------------------------------------------------
-- | 'SymEnv' is used to resolve the 'Sort' and 'Sem' of each 'Symbol'
--------------------------------------------------------------------------------
data SymEnv = SymEnv
  { seSort   :: SEnv Sort
  , seTheory :: SEnv TheorySymbol
  }

instance Monoid SymEnv where
  mempty        = SymEnv emptySEnv emptySEnv
  mappend e1 e2 = SymEnv { seSort   = seSort   e1 `mappend` seSort e2
                         , seTheory = seTheory e1 `mappend` seTheory e2
                         }

symEnv :: SEnv Sort -> SEnv TheorySymbol -> SymEnv
symEnv = SymEnv

symEnvTheory :: Symbol -> SymEnv -> Maybe TheorySymbol
symEnvTheory x (SymEnv _ env) = lookupSEnv x env

symEnvSort :: Symbol -> SymEnv -> Maybe Sort
symEnvSort x (SymEnv env _) = lookupSEnv x env

insertSymEnv :: Symbol -> Sort -> SymEnv -> SymEnv
insertSymEnv x t env = env { seSort = insertSEnv x t (seSort env) }

--------------------------------------------------------------------------------
-- | 'TheorySymbol' represents the information about each interpreted 'Symbol'
--------------------------------------------------------------------------------
data TheorySymbol  = Thy
  { tsSym    :: !Symbol          -- ^ name
  , tsRaw    :: !Raw             -- ^ serialized SMTLIB2 name
  , tsSort   :: !Sort            -- ^ sort
  , tsInterp :: !Sem             -- ^ TRUE = defined (interpreted), FALSE = declared (uninterpreted)
  }
  deriving (Eq, Ord, Show)



--------------------------------------------------------------------------------
-- | 'Sem' describes the SMT semantics for a given symbol
--------------------------------------------------------------------------------

data Sem
  = Uninterp                     -- ^ for UDF: `len`, `height`, `append`
  | Data                         -- ^ for ADT ctors & accessor: `cons`, `nil`, `head`
  | Theory                       -- ^ for theory ops: mem, cup, select
  deriving (Eq, Ord, Show)
