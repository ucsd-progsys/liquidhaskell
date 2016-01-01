{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE TupleSections       #-}
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

  -- * Error with Source Context
  , CtxError (..)
  , errorWithContext

  -- * Subtyping Obligation Type
  , Oblig (..)

  -- * Misc Creators & Transformers
  , errToFCrash

  -- * Panic (unexpected failures)
  , Panic (..)
  , panic
  , todo
  , impossible

  ) where

import           Type
import           SrcLoc                       (noSrcSpan, SrcSpan)
import           GHC.Generics
import           Data.Typeable                (Typeable)
import           Data.Generics                (Data)
import           Data.Generics.Schemes        (everywhere)
import           Data.Generics.Aliases        (mkT)
import           Data.Maybe
import           Data.Bifunctor
import qualified Data.Text as T
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict as M

import           Language.Fixpoint.Types               (showpp, PPrint (..), Symbol, Expr, Reft)
import           Language.Haskell.Liquid.GHC.Misc      (pprDoc)
import           Language.Haskell.Liquid.GHC.SpanStack (showSpan)
import           Text.Parsec.Error            (ParseError)
import qualified Control.Exception as Ex
import qualified Control.Monad.Error as Ex

--------------------------------------------------------------------------------
-- | Context information for Error Messages ------------------------------------
--------------------------------------------------------------------------------
errorWithContext :: TError t -> IO (CtxError t)
--------------------------------------------------------------------------------
errorWithContext e = CtxError e <$> srcSpanContext (pos e)

data CtxError t = CtxError {
    ctErr :: TError t
  , ctCtx :: Doc
  }

srcSpanContext :: SrcSpan -> IO Doc
srcSpanContext = "TODO: HEREHEREHERE addContext"

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

data TError t =
    ErrSubType { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrFCrash  { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrAssType { pos  :: !SrcSpan
               , obl  :: !Oblig
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , cond :: !Reft
               } -- ^ condition failure error

  | ErrParse    { pos  :: !SrcSpan
                , msg  :: !Doc
                , pErr :: !ParseError
                } -- ^ specification parse error

  | ErrTySpec   { pos :: !SrcSpan
                , var :: !Doc
                , typ :: !t
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrTermSpec { pos :: !SrcSpan
                , var :: !Doc
                , exp :: !Expr
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrDupAlias { pos  :: !SrcSpan
                , var  :: !Doc
                , kind :: !Doc
                , locs :: ![SrcSpan]
                } -- ^ multiple alias with same name error

  | ErrDupSpecs { pos :: !SrcSpan
                , var :: !Doc
                , locs:: ![SrcSpan]
                } -- ^ multiple specs for same binder error

  | ErrBadData  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ multiple specs for same binder error

  | ErrInvt     { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Invariant sort error

  | ErrIAl      { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Using  sort error

  | ErrIAlMis   { pos :: !SrcSpan
                , t1  :: !t
                , t2  :: !t
                , msg :: !Doc
                } -- ^ Incompatible using error

  | ErrMeas     { pos :: !SrcSpan
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Measure sort error

  | ErrHMeas    { pos :: !SrcSpan
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Haskell bad Measure error

  | ErrUnbound  { pos :: !SrcSpan
                , var :: !Doc
                } -- ^ Unbound symbol in specification

  | ErrGhc      { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ GHC error: parsing or type checking

  | ErrMismatch { pos  :: !SrcSpan
                , var  :: !Doc
                , hs   :: !Type
                , lq   :: !Type
                } -- ^ Mismatch between Liquid and Haskell types

  | ErrAliasCycle { pos    :: !SrcSpan
                  , acycle :: ![(SrcSpan, Doc)]
                  } -- ^ Cyclic Refined Type Alias Definitions

  | ErrIllegalAliasApp { pos   :: !SrcSpan
                       , dname :: !Doc
                       , dpos  :: !SrcSpan
                       } -- ^ Illegal RTAlias application (from BSort, eg. in PVar)

  | ErrAliasApp { pos   :: !SrcSpan
                , nargs :: !Int
                , dname :: !Doc
                , dpos  :: !SrcSpan
                , dargs :: !Int
                }

  | ErrSaved    { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ Previously saved error, that carries over after DiffCheck

  | ErrTermin   { pos  :: !SrcSpan
                , bind :: ![Var]
                , msg  :: !Doc
                } -- ^ Termination Error

  | ErrRClass   { pos   :: !SrcSpan
                , cls   :: !Doc
                , insts :: ![(SrcSpan, Doc)]
                } -- ^ Refined Class/Interfaces Conflict

  | ErrBadQual  { pos   :: !SrcSpan
                , qname :: !Doc
                , msg   :: !Doc
                } -- ^ Non well sorted Qualifier

  | ErrOther    { pos   :: SrcSpan
                , msg   :: !Doc
                } -- ^ Sigh. Other.

  deriving (Typeable, Generic, Functor)

instance Eq (TError a) where
  e1 == e2 = errSpan e1 == errSpan e2

instance Ord (TError a) where
  e1 <= e2 = errSpan e1 <= errSpan e2

errSpan :: TError a -> SrcSpan
errSpan =  pos

instance Ex.Error (TError a) where
   strMsg = ErrOther (showSpan "Yikes! Exception!") . text

errToFCrash :: TError a -> TError a
errToFCrash (ErrSubType l m g t t') = ErrFCrash l m g t t'
errToFCrash e                       = e

--------------------------------------------------------------------------------
-- | Simple unstructured type for panic ----------------------------------------
--------------------------------------------------------------------------------

data Panic = Panic { ePos :: !SrcSpan
                   , eMsg :: !Doc
                   } -- ^ Unexpected PANIC
  deriving (Typeable)

instance PPrint SrcSpan where
  pprint = pprDoc

instance PPrint Panic where
  pprint (Panic sp d) = pprint sp <+> text "Unexpected panic (!)"
                                  $+$ nest 4 d

instance Show Panic where
  show = showpp

instance Ex.Exception Panic

-- | Construct and show an Error, then crash
panic :: {-(?callStack :: CallStack) =>-} Maybe SrcSpan -> String -> a
panic sp d = Ex.throw $ Panic (sspan sp) (text d)
  where
    sspan  = fromMaybe noSrcSpan


-- | Construct and show an Error with no SrcSpan, then crash
--   This function should be used to mark unimplemented functionality
todo :: {-(?callStack :: CallStack) =>-} String -> a
todo m = panic Nothing $ "TODO: " ++ m

-- | Construct and show an Error with no SrcSpan, then crash
--   This function should be used to mark impossible-to-reach codepaths
impossible :: {-(?callStack :: CallStack) =>-} String -> a
impossible  m = panic Nothing $ "Should never happen: " ++ m
