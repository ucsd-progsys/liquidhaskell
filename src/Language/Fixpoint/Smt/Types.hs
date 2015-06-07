{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Smt.Types (

    -- * Serialized Representation
      Raw

    -- * Commands
    , Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)

    -- * SMTLIB2 Process Context
    , Context (..)

    -- * Theory Symbol
    , TheorySymbol (..)

    ) where

import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Errors
import           Language.Fixpoint.Files
import           Language.Fixpoint.Types

import           Control.Applicative      ((*>), (<$>), (<*), (<|>))
import           Control.Monad
import           Data.Char
import qualified Data.HashMap.Strict      as M
import qualified Data.List                as L
import           Data.Monoid
import qualified Data.Text                as T
import           Data.Text.Format
import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (Handle, IOMode (..), hClose, hFlush,
                                           openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A

--------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------
--------------------------------------------------------------------------

type Raw          = T.Text

-- | Commands issued to SMT engine
data Command      = Push
                  | Pop
                  | CheckSat
                  | Declare   Symbol [Sort] Sort
                  | Define    Sort
                  | Assert    (Maybe Int) Pred
                  | Distinct  [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue  [Symbol]
                  deriving (Eq, Show)

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, Raw)]
                  | Error Raw
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context      = Ctx { pId     :: ProcessHandle
                        , cIn     :: Handle
                        , cOut    :: Handle
                        , cLog    :: Maybe Handle
                        , verbose :: Bool
                        }

-- | Theory Symbol
data TheorySymbol  = Thy { tsSym  :: Symbol
                         , tsRaw  :: Raw
                         , tsSort :: Sort
                         }
                     deriving (Eq, Ord, Show)

-----------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ---------------------
-----------------------------------------------------------------------

-- | Types that can be serialized
class SMTLIB2 a where
  smt2 :: a -> LT.Text

