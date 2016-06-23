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
    , runSmt2
    
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
                        , c_ext   :: !Bool              -- flag to enable function extentionality axioms
                        , smtenv  :: !SMTEnv
                        }

-- | Theory Symbol
data TheorySymbol  = Thy { tsSym  :: !Symbol
                         , tsRaw  :: !Raw
                         , tsSort :: !Sort
                         }
                     deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ------------------------------
--------------------------------------------------------------------------------

type SMTEnv = SEnv Sort
data SMTSt  = SMTSt {fresh :: !Int , smt2env :: !SMTEnv, f_ext :: !Bool}

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
  n  <- fresh <$> get
  modify $ \s -> s{fresh = n + 1}
  return $ intSymbol "lambda_fun_" n

{- 
-- Proper Handing of Lam Arguments
freshLamSym :: (Symbol,Sort) -> Expr  -> SMT2 (Expr, Maybe Symbol) 
freshLamSym (x, s) e = do 
  ss <- M.lookup s . globals <$> get
  case ss of 
    Nothing -> do y <- freshSym
                  modify $ \st -> st{globals = M.insert s [y] (globals st)}
                  return (ELam (y, s) $ e `subst1` (x, EVar y), Just y)
    Just xs -> 
               if length xs <= i then do 
                  y <- freshSym
                  insertLamSym s y 
                  return (ELam (y, s) $ e `subst1` (x, EVar y), Just y)
               else 
                  return (ELam (xs!!i, s) $ e `subst1` (x, EVar (xs!!i)), Nothing)
  where
    i  = go e
    go (ELam (_, s') e) | s == s' = 1 + go e 
    go (ELam _ e)   = go e 
    go (ECst e _)   = go e 
    go (EApp e1 e2) = (go e1) + (go e2)
    -- go ... 
    go _            = 0 


insertLamSym :: Sort -> Symbol -> SMT2 () 
insertLamSym s y = 
  modify $ \st -> st{globals = M.insertWith (flip (++)) s [y] (globals st)}

-}
-- | Types that can be serialized
class SMTLIB2 a where
  defunc :: a -> SMT2 a
  defunc = return

  smt2 :: a -> LT.Builder

runSmt2 :: (SMTLIB2 a) => Int -> Context -> a -> LT.Builder
runSmt2 n cxt a = smt2 $ evalState (defunc a) (SMTSt n (smtenv cxt) (c_ext cxt))
