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

    -- * Strict Formatter
    , format

    ) where

import           Language.Fixpoint.Types
import qualified Data.Text.Format         as DTF
import           Data.Text.Format.Params  (Params)
import qualified Data.Text                as T
import qualified Data.Text.Lazy           as LT
import           System.IO                (Handle)
import           System.Process
import           Control.Monad.State

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
                  | Assert    (Maybe Int) Expr
                  | Distinct  [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue  [Symbol]
                  | CMany [Command]
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
                        , smtenv  :: SMTEnv
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

format :: Params ps => DTF.Format -> ps -> T.Text
format f x = LT.toStrict $ DTF.format f x

type SMTEnv = SEnv Sort 
data SMTSt  = SMTSt {fresh :: Int , smt2env :: SMTEnv}

type SMT2   = State SMTSt

emptySMTEnv = emptySEnv 

withExtendedEnv bs act = do 
  env <- smt2env <$> get 
  let env' = foldl (\env (x, t) -> insertSEnv x t env) env bs
  modify $ \s -> s{smt2env = env'}
  r <- act 
  modify $ \s -> s{smt2env = env}
  return r 

freshSym = do 
  n <- fresh <$> get 
  modify $ \s -> s{fresh = n + 1}
  return $ intSymbol "lambda_fun_" n 

-- | Types that can be serialized
class SMTLIB2 a where
  defunc :: a -> SMT2 a
  defunc = return 

  smt2 :: a -> T.Text 

  runSmt2 :: SMTEnv -> a -> T.Text 
  runSmt2 env a = smt2 $ evalState (defunc a) (SMTSt 0 env)
