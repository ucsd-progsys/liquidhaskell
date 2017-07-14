{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Test.Target.Types where

import qualified Control.Monad.Catch             as Ex
import qualified Data.Set                        as S
import qualified Data.Text                       as T
import           Data.Typeable
import           GHC.Generics
import           Text.PrettyPrint

import           Language.Fixpoint.Smt.Interface
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types

import           GHC

-- import           Test.Target.Serialize



data TargetException
  = SmtFailedToProduceOutput
  | SmtError String
  | ExpectedValues Response
  | PreconditionCheckFailed String
  | EvalError String
  deriving Typeable

instance Show TargetException where
  show SmtFailedToProduceOutput
    = "The SMT solver was unable to produce an output value."
  show (SmtError s)
    = "Unexpected error from the solver: " ++ s
  show (ExpectedValues r)
    = "Expected a Values response from the solver, got: " ++ show r
  show (PreconditionCheckFailed e)
    = "The pre-condition check for a generated function failed: " ++ e
  show (EvalError s)
    = "Couldn't evaluate a concrete refinement: " ++ s

instance Ex.Exception TargetException

ensureValues :: Ex.MonadThrow m => m Response -> m Response
ensureValues x = do
  a <- x
  case a of
    Values _ -> return a
    r        -> Ex.throwM $ ExpectedValues r

type Constraint = [Expr]
type Variable   = ( Symbol -- the name
                  , Sort   -- the `Sort'
                  )
type Value      = T.Text

instance Symbolic Variable where
  symbol (x, _) = symbol x

instance SMTLIB2 Constraint where
  smt2 env = smt2 env . PAnd

type DataConEnv = [(Symbol, SpecType)]
type MeasureEnv = [Measure SpecType DataCon]

boolsort, choicesort :: Sort
boolsort   = FObj "Bool"
choicesort = FObj "CHOICE"

data Result = Passed !Int
            | Failed !String
            | Errored !String
            deriving (Show, Typeable)

-- resultPassed (Passed i) = i

data Val
  = VB !Bool
  | VV !Constant
  | VX !SymConst
  | VS !(S.Set Val) -- ??
  | VC Symbol [Val]
  deriving (Generic, Show, Eq, Ord)

instance PPrint Val where
  pprintTidy t (VB b) = pprintTidy t b
  pprintTidy t (VV v) = pprintTidy t v
  pprintTidy t (VX x) = pprintTidy t x
  pprintTidy t (VS s) = "Set.fromList" <+> pprintTidy t (S.toList s)
  pprintTidy t (VC c vs) = parens $ pprintTidy t c <+> hsep (map (pprintTidy t) vs)
