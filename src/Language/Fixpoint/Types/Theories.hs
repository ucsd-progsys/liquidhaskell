{- LANGUAGE FlexibleInstances         #-}
{- LANGUAGE FlexibleContexts          #-}
{- LANGUAGE NoMonomorphismRestriction #-}
{- LANGUAGE OverloadedStrings         #-}
{- LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveDataTypeable         #-}

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
    , symEnvData
    , insertSymEnv

    ) where


import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Control.DeepSeq
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Environments

import           Text.PrettyPrint.HughesPJ
import qualified Data.Text.Lazy           as LT
import qualified Data.Binary as B

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
  , seData   :: SEnv DataDecl
  }
  deriving (Eq, Show, Data, Typeable, Generic)

instance NFData   SymEnv
instance B.Binary SymEnv

instance Monoid SymEnv where
  mempty        = SymEnv emptySEnv emptySEnv emptySEnv
  mappend e1 e2 = SymEnv { seSort   = seSort   e1 `mappend` seSort   e2
                         , seTheory = seTheory e1 `mappend` seTheory e2
                         , seData   = seData   e1 `mappend` seData   e2
                         }

symEnv :: SEnv Sort -> SEnv TheorySymbol -> [DataDecl] -> SymEnv
symEnv xEnv fEnv ds = SymEnv xEnv fEnv dEnv
  where
    dEnv            = fromListSEnv [(symbol d, d) | d <- ds]

symEnvTheory :: Symbol -> SymEnv -> Maybe TheorySymbol
symEnvTheory x env = lookupSEnv x (seTheory env)

symEnvSort :: Symbol -> SymEnv -> Maybe Sort
symEnvSort   x env = lookupSEnv x (seSort env)

symEnvData :: FTycon -> SymEnv -> Bool
symEnvData c env = memberSEnv (symbol c) (seData env)

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
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance NFData Sem
instance NFData TheorySymbol
instance B.Binary TheorySymbol

instance PPrint Sem where
  pprintTidy _ = text . show

instance Fixpoint TheorySymbol where
  toFix (Thy x _ t d) = text "TheorySymbol" <+> pprint (x, t) <+> parens (pprint d)

instance PPrint TheorySymbol where
  pprintTidy k (Thy x _ t d) = text "TheorySymbol" <+> pprintTidy k (x, t) <+> parens (pprint d)

--------------------------------------------------------------------------------
-- | 'Sem' describes the SMT semantics for a given symbol
--------------------------------------------------------------------------------

data Sem
  = Uninterp                     -- ^ for UDF: `len`, `height`, `append`
  | Data                         -- ^ for ADT ctors & accessor: `cons`, `nil`, `head`
  | Theory                       -- ^ for theory ops: mem, cup, select
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance B.Binary Sem
