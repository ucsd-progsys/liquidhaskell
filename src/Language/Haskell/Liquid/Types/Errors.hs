{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFunctor       #-}

-- | This module contains the *types* related creating Errors.
--   It depends only on Fixpoint and basic haskell libraries,
--   and hence, should be importable everywhere.

module Language.Haskell.Liquid.Types.Errors (
  -- * Generic Error Type
    TError (..)

  -- * Subtyping Obligation Type
  , Oblig (..)

  -- * Source Span Information
  , SourceInfo (..)
  , CtxSpan (..)

  -- * Misc Creators & Transformers
  , errOther
  , errToFCrash

  -- * Various ways to die
  , panic
  , panicError
  , todo
  , impossible
  ) where

import           Type
import           SrcLoc                       (noSrcSpan, SrcSpan)
import           GHC.Generics
import           Data.Typeable                (Typeable)
import           Data.Generics                (Data)
import           Data.Maybe
import qualified Data.Text as T
import qualified Control.Monad.Error as Ex
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict as M
import           Language.Fixpoint.Types      (Symbol, Expr)
import           Text.Parsec.Error            (ParseError)

--------------------------------------------------------------------------------
-- | A million ways to die -----------------------------------------------------
--------------------------------------------------------------------------------

-- | Show an Error, then crash
panicError :: {-(?callStack :: CallStack) =>-} Error -> a
panicError = Ex.throw

-- | Construct and show an Error, then crash
panic :: {-(?callStack :: CallStack) =>-} Maybe SrcSpan -> String -> a
panic sp d = panicError $ errOther sp $ text d

-- | Construct and show an Error with no SrcSpan, then crash
--   This function should be used to mark unimplemented functionality
todo :: {-(?callStack :: CallStack) =>-} String -> a
todo m = panic Nothing $ "TODO: " ++ m

-- | Construct and show an Error with no SrcSpan, then crash
--   This function should be used to mark impossible-to-reach codepaths
impossible :: {-(?callStack :: CallStack) =>-} String -> a
impossible  m = panic Nothing $ "Should never happen: " ++ m

--------------------------------------------------------------------------------
-- | Context information for Error Messages ------------------------------------
--------------------------------------------------------------------------------

class SourceInfo s where
  siSpan    :: s -> SrcSpan
  siContext :: s -> Doc

instance SourceInfo SrcSpan where
  siSpan x    = x
  siContext _ = empty

data CtxSpan = CtxSpan
  { ctSpan    :: SrcSpan
  , ctContext :: T.Text
  } deriving (Generic)

instance SourceInfo CtxSpan where
  siSpan    = ctSpan
  siContext = text . T.unpack . ctContext


--------------------------------------------------------------------------------
-- | Different kinds of Check "Obligations" ------------------------------------
--------------------------------------------------------------------------------

data Oblig
  = OTerm -- ^ Obligation that proves termination
  | OInv  -- ^ Obligation that proves invariants
  | OCons -- ^ Obligation that proves subtyping constraints
  deriving (Generic, Data, Typeable)


instance Show Oblig where
  show OTerm = "termination-condition"
  show OInv  = "invariant-obligation"
  show OCons = "constraint-obligation"


--------------------------------------------------------------------------------
-- | Generic Type for Error Messages -------------------------------------------
--------------------------------------------------------------------------------

-- | INVARIANT : all Error constructors should have a pos field

data TError s t =
    ErrSubType { pos  :: s
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrFCrash  { pos  :: s
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrAssType { pos  :: s
               , obl  :: !Oblig
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , cond :: !Doc -- RReft
               } -- ^ condition failure error

  | ErrParse    { pos  :: s
                , msg  :: !Doc
                , pErr :: !ParseError
                } -- ^ specification parse error

  | ErrTySpec   { pos :: s
                , var :: !Doc
                , typ :: !t
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrTermSpec { pos :: s
                , var :: !Doc
                , exp :: !Expr
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrDupAlias { pos  :: s
                , var  :: !Doc
                , kind :: !Doc
                , locs :: ![s]
                } -- ^ multiple alias with same name error

  | ErrDupSpecs { pos :: s
                , var :: !Doc
                , locs:: ![s]
                } -- ^ multiple specs for same binder error

  | ErrBadData  { pos :: s
                , var :: !Doc
                , msg :: !Doc
                } -- ^ multiple specs for same binder error

  | ErrInvt     { pos :: s
                , inv :: !t
                , msg :: !Doc
                } -- ^ Invariant sort error

  | ErrIAl      { pos :: s
                , inv :: !t
                , msg :: !Doc
                } -- ^ Using  sort error

  | ErrIAlMis   { pos :: s
                , t1  :: !t
                , t2  :: !t
                , msg :: !Doc
                } -- ^ Incompatible using error

  | ErrMeas     { pos :: s
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Measure sort error

  | ErrHMeas    { pos :: s
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Haskell bad Measure error

  | ErrUnbound  { pos :: s
                , var :: !Doc
                } -- ^ Unbound symbol in specification

  | ErrGhc      { pos :: s
                , msg :: !Doc
                } -- ^ GHC error: parsing or type checking

  | ErrMismatch { pos  :: s
                , var  :: !Doc
                , hs   :: !Type
                , lq   :: !Type
                } -- ^ Mismatch between Liquid and Haskell types

  | ErrAliasCycle { pos    :: s
                  , acycle :: ![(s, Doc)]
                  } -- ^ Cyclic Refined Type Alias Definitions

  | ErrIllegalAliasApp { pos   :: s
                       , dname :: !Doc
                       , dpos  :: s
                       } -- ^ Illegal RTAlias application (from BSort, eg. in PVar)

  | ErrAliasApp { pos   :: s
                , nargs :: !Int
                , dname :: !Doc
                , dpos  :: s
                , dargs :: !Int
                }

  | ErrSaved    { pos :: s
                , msg :: !Doc
                } -- ^ Previously saved error, that carries over after DiffCheck

  | ErrTermin   { pos  :: s
                , bind :: ![Var]
                , msg  :: !Doc
                } -- ^ Termination Error

  | ErrRClass   { pos   :: s
                , cls   :: !Doc
                , insts :: ![(SrcSpan, Doc)]
                } -- ^ Refined Class/Interfaces Conflict

  | ErrBadQual  { pos   :: s
                , qname :: !Doc
                , msg   :: !Doc
                } -- ^ Non well sorted Qualifier

  | ErrOther    { pos :: s
                , msg :: !Doc
                } -- ^ Unexpected PANIC
  deriving (Typeable, Functor)

instance (SourceInfo s) => Eq (TError s a) where
  e1 == e2 = errSpan e1 == errSpan e2

instance (SourceInfo s) => Ord (TError s a) where
  e1 <= e2 = errSpan e1 <= errSpan e2

errSpan :: (SourceInfo s) => TError s a -> SrcSpan
errSpan = siSpan . pos

instance Ex.Error (TError SrcSpan a) where
  strMsg = errOther Nothing . text

errOther :: Maybe SrcSpan -> Doc -> TError SrcSpan a
errOther = ErrOther . fromMaybe noSrcSpan

errToFCrash :: TError s a -> TError s a
errToFCrash (ErrSubType l m g t1 t2) = ErrFCrash l m g t1 t2
errToFCrash e                        = e
