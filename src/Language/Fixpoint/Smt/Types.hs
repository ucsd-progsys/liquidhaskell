{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Smt.Types (

    -- * Serialized Representation
      Raw
    , symbolBuilder

    -- * Commands
    , Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)
    , runSmt2

    -- * SMTLIB2 Process Context
    , Context (..)

    -- * Theory Symbol
    , TheorySymbol (..)
    , SMTEnv
    ) where

import           Language.Fixpoint.Types
-- import           Language.Fixpoint.Misc   (traceShow)
import qualified Data.Text                as T
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.Builder   as LT
import           Text.PrettyPrint.HughesPJ 

import           System.IO                (Handle)
import           System.Process

--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------
type Raw          = LT.Text

symbolBuilder :: Symbol -> LT.Builder
symbolBuilder = LT.fromText . symbolSafeText

-- | Commands issued to SMT engine
data Command      = Push
                  | Pop
                  | CheckSat
                  | Declare   !Symbol [Sort] !Sort
                  | Define    !Sort
                  | Assert    !(Maybe Int) !Expr
                  | Distinct  [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue  [Symbol]
                  | CMany [Command]
                  deriving (Eq, Show)

instance PPrint Command where
  pprintTidy _ = ppCmd

ppCmd :: Command -> Doc
ppCmd Push          = text "Push"
ppCmd Pop           = text "Pop"
ppCmd CheckSat      = text "CheckSat"
ppCmd (Declare {})  = text "Declare ..."
ppCmd (Define {})   = text "Define ..."
ppCmd (Assert _ e)  = text "Assert" <+> pprint e
ppCmd (Distinct {}) = text "Distinct ..."
ppCmd (GetValue {}) = text "GetValue ..."
ppCmd (CMany {})    = text "CMany ..."

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, T.Text)]
                  | Error !T.Text
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context = Ctx
  { ctxPid     :: !ProcessHandle
  , ctxCin     :: !Handle
  , ctxCout    :: !Handle
  , ctxLog     :: !(Maybe Handle)
  , ctxVerbose :: !Bool
  , ctxExt     :: !Bool              -- ^ flag to enable function extentionality axioms
  , ctxAeq     :: !Bool              -- ^ flag to enable lambda a-equivalence axioms
  , ctxBeq     :: !Bool              -- ^ flag to enable lambda b-equivalence axioms
  , ctxNorm    :: !Bool              -- ^ flag to enable lambda normal form equivalence axioms
  , ctxSmtEnv  :: !SMTEnv
  }

type SMTEnv = SEnv Sort

-- | Theory Symbol
data TheorySymbol  = Thy
  { tsSym    :: !Symbol    -- ^ name
  , tsRaw    :: !Raw       -- ^ serialized SMTLIB2 name
  , tsSort   :: !Sort      -- ^ sort
  , tsInterp :: !Bool      -- ^ TRUE = defined (interpreted), FALSE = declared (uninterpreted)
  }
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ------------------------------
--------------------------------------------------------------------------------

class SMTLIB2 a where
  smt2 :: a -> LT.Builder

runSmt2 :: (SMTLIB2 a) => a -> LT.Builder
runSmt2 = smt2
