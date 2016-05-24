{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
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

    -- * SMTLIB2 symbol environment
    , SMTEnv, emptySMTEnv, SMTSt(..), withExtendedEnv, SMT2, freshSym

    -- * Theory Symbol
    , TheorySymbol (..)
    ) where

import           Language.Fixpoint.Types
-- import           Language.Fixpoint.Misc   (traceShow)
import qualified Data.Text                as T
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.Builder   as LT
import           System.IO                (Handle)
import           System.Process
import           Control.Monad.State

--------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------
--------------------------------------------------------------------------

type Raw          = LT.Text

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

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, T.Text)]
                  | Error !T.Text
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context      = Ctx { pId     :: !ProcessHandle
                        , cIn     :: !Handle
                        , cOut    :: !Handle
                        , cLog    :: !(Maybe Handle)
                        , verbose :: !Bool
                        , smtenv  :: !SMTEnv
                        }

-- | Theory Symbol
data TheorySymbol  = Thy { tsSym  :: !Symbol
                         , tsRaw  :: !Raw
                         , tsSort :: !Sort
                         }
                     deriving (Eq, Ord, Show)

-----------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ---------------------
-----------------------------------------------------------------------

type SMTEnv = SEnv Sort
data SMTSt  = SMTSt {fresh :: !Int , smt2env :: !SMTEnv}

type SMT2   = State SMTSt

emptySMTEnv :: SMTEnv
emptySMTEnv = emptySEnv

withExtendedEnv ::  [(Symbol, Sort)] -> SMT2 a -> SMT2 a
withExtendedEnv bs act = do
  env <- smt2env <$> get
  let env' = foldl (\env (x, t) -> insertSEnv x t env) env bs
  modify $ \s -> s{smt2env = env'}
  r <- act
  modify $ \s -> s{smt2env = env}
  return r

freshSym :: SMT2 Symbol
freshSym = do
  n <- fresh <$> get
  modify $ \s -> s{fresh = n + 1}
  return $ intSymbol "lambda_fun_" n

-- | Types that can be serialized
class SMTLIB2 a where
  defunc :: a -> SMT2 a
  defunc = return

  smt2 :: a -> LT.Builder

  runSmt2 :: Int -> SMTEnv -> a -> LT.Builder
  runSmt2 n env a = smt2 $ evalState (defunc a) (SMTSt n env)
