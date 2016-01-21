{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}

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

  -- * Panic (unexpected failures)
  , Panic (..)
  , panic
  , todo
  , impossible

  ) where

import           Prelude                      hiding (error)
import           Type
import           SrcLoc                      -- (SrcSpan (..), noSrcSpan)
import           FastString
import           GHC.Generics
import           Control.DeepSeq
import           Data.Typeable                (Typeable)
import           Data.Generics                (Data)
import           Data.Maybe
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict as M
import           Language.Fixpoint.Types               (showpp, PPrint (..), Symbol, Expr, Reft)
import           Text.Parsec.Error            (ParseError)
import qualified Control.Exception as Ex
import qualified Control.Monad.Error as Ex
import qualified Outputable as Out
import           DynFlags (unsafeGlobalDynFlags)

--------------------------------------------------------------------------------
-- | Context information for Error Messages ------------------------------------
--------------------------------------------------------------------------------
data CtxError t = CtxError
  { ctErr :: TError t
  , ctCtx :: Doc
  } deriving (Functor)

instance Eq (CtxError t) where
  e1 == e2 = ctErr e1 == ctErr e2

instance Ord (CtxError t) where
  e1 <= e2 = ctErr e1 <= ctErr e2

--------------------------------------------------------------------------------
errorWithContext :: TError t -> IO (CtxError t)
--------------------------------------------------------------------------------
errorWithContext e = CtxError e <$> srcSpanContext (pos e)

srcSpanContext :: SrcSpan -> IO Doc
srcSpanContext sp
  | Just (f, l, c, c') <- srcSpanInfo sp
  = maybe empty (makeContext l c c') <$> getFileLine f l
  | otherwise
  = return empty

srcSpanInfo :: SrcSpan -> Maybe (FilePath, Int, Int, Int)
srcSpanInfo (RealSrcSpan s)
  | l == l'           = Just (f, l, c, c')
  | otherwise         = Nothing
  where
     f  = unpackFS $ srcSpanFile s
     l  = srcSpanStartLine s
     c  = srcSpanStartCol  s
     l' = srcSpanEndLine   s
     c' = srcSpanEndCol    s
srcSpanInfo _         = Nothing

getFileLine :: FilePath -> Int -> IO (Maybe String)
getFileLine f i = getNth (i - 1) . lines <$> readFile f

getNth :: Int -> [a] -> Maybe a
getNth i xs
  | i < length xs = Just (xs !! i)
  | otherwise     = Nothing

makeContext :: Int -> Int -> Int -> String -> Doc
makeContext l c c' s = vcat [ text ""
                            , lnum l <+> (text s $+$ cursor)
                            , text ""
                            ]
  where
    lnum n           = text (show n) <+> text "|"
    cursor           = blanks (c - 1) <> pointer (c' - c)
    blanks n         = text $ replicate n ' '
    pointer n        = text $ replicate n '^'

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

instance NFData Oblig


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

instance NFData ParseError where
  rnf t = seq t ()

-- FIXME ES: this is very suspicious, why can't we have multiple errors
-- arising from the same span?

instance Eq (TError a) where
  e1 == e2 = errSpan e1 == errSpan e2

instance Ord (TError a) where
  e1 <= e2 = errSpan e1 <= errSpan e2


errSpan :: TError a -> SrcSpan
errSpan =  pos

showSpan' :: (Show a) => a -> SrcSpan
showSpan' = mkGeneralSrcSpan . fsLit . show

instance Ex.Error (TError a) where
   strMsg = ErrOther (showSpan' "Yikes! Exception!") . text


--------------------------------------------------------------------------------
-- | Simple unstructured type for panic ----------------------------------------
--------------------------------------------------------------------------------

data Panic = Panic { ePos :: !SrcSpan
                   , eMsg :: !Doc
                   } -- ^ Unexpected PANIC
  deriving (Typeable, Generic)

instance PPrint SrcSpan where
  pprint = text . showSDoc . Out.ppr
     where
        showSDoc sdoc = Out.renderWithStyle
                        unsafeGlobalDynFlags
                        sdoc (Out.mkUserStyle
                              Out.alwaysQualify
                              Out.AllTheWay)

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


-- | Construct and show an Error with an optional SrcSpan, then crash
--   This function should be used to mark unimplemented functionality
todo :: {-(?callStack :: CallStack) =>-} Maybe SrcSpan -> String -> a
todo s m  = panic s $ unlines
            [ "This functionality is currently unimplemented. "
            , "If this functionality is critical to you, please contact us at: "
            , "https://github.com/ucsd-progsys/liquidhaskell/issues"
            , m
            ]

-- | Construct and show an Error with an optional SrcSpan, then crash
--   This function should be used to mark impossible-to-reach codepaths
impossible :: {-(?callStack :: CallStack) =>-} Maybe SrcSpan -> String -> a
impossible s m = panic s $ unlines msg ++ m
   where
      msg = [ "This should never happen! If you are seeing this message, "
            , "please submit a bug report at "
            , "https://github.com/ucsd-progsys/liquidhaskell/issues "
            , "with this message and the source file that caused this error."
            , ""
            ]
