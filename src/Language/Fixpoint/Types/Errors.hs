{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE OverloadedStrings         #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Fixpoint.Types.Errors (
  -- * Concrete Location Type
    SrcSpan (..)
  , dummySpan
  , sourcePosElts

  -- * Result

  , FixResult (..)
  , colorResult
  , resultDoc

  -- * Abstract Error Type
  , Error

  -- * Constructor
  , err

  -- * Accessors
  , errLoc
  , errMsg

  -- * Adding Insult to Injury
  , catError
  , catErrors

  -- * Fatal Exit
  , panic
  , die
  , dieAt
  , exit

  -- * Some popular errors
  , errFreeVarInQual
  , errFreeVarInConstraint
  , errIllScopedKVar
  ) where

import           Control.Exception
import           Data.Serialize                (Serialize (..))
import           Data.Generics                 (Data)
import           Data.Typeable
import           Control.DeepSeq
-- import           Data.Hashable
import qualified Data.Binary                   as B
import           GHC.Generics                  (Generic)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ
-- import           Text.Printf
import           Data.Function (on)

-- import           Debug.Trace

#if MIN_VERSION_pretty(1,1,3)
import qualified Text.PrettyPrint.Annotated.HughesPJ as Ann

deriving instance Generic (Ann.AnnotDetails a)
instance Serialize a => Serialize (Ann.AnnotDetails a)
instance Serialize a => Serialize (Ann.Doc a)
#endif

instance Serialize Error1
-- FIXME: orphans are bad...
instance Serialize TextDetails

instance Serialize Doc
instance Serialize Error
instance Serialize (FixResult Error)

instance (B.Binary a) => B.Binary (FixResult a)

--------------------------------------------------------------------------------
-- | A BareBones Error Type ----------------------------------------------------
--------------------------------------------------------------------------------

newtype Error = Error [Error1]
                deriving (Eq, Ord, Show, Typeable, Generic)

data Error1 = Error1
  { errLoc :: SrcSpan
  , errMsg :: Doc
  } deriving (Eq, Show, Typeable, Generic)

instance Ord Error1 where
  compare = compare `on` errLoc

instance PPrint Error1 where
  pprintTidy k (Error1 l msg) = (pprintTidy k l <> ": Error")
                                $+$ nest 2 msg

instance PPrint Error where
  pprintTidy k (Error es) = vcat $ pprintTidy k <$> es

instance Fixpoint Error1 where
  toFix = pprint

instance Exception Error
instance Exception (FixResult Error)


---------------------------------------------------------------------
catError :: Error -> Error -> Error
---------------------------------------------------------------------
catError (Error e1) (Error e2) = Error (e1 ++ e2)

---------------------------------------------------------------------
catErrors :: ListNE Error -> Error
---------------------------------------------------------------------
catErrors = foldr1 catError

---------------------------------------------------------------------
err :: SrcSpan -> Doc -> Error
---------------------------------------------------------------------
err sp d = Error [Error1 sp d]

---------------------------------------------------------------------
panic :: String -> a
---------------------------------------------------------------------
panic = die . err dummySpan . text . (panicMsg ++)

panicMsg :: String
panicMsg = "PANIC: Please file an issue at https://github.com/ucsd-progsys/liquid-fixpoint \n"

---------------------------------------------------------------------
die :: Error -> a
---------------------------------------------------------------------
die = throw

---------------------------------------------------------------------
dieAt :: SrcSpan -> Error -> a
---------------------------------------------------------------------
dieAt sp (Error es) = die (Error [ e {errLoc = sp} | e <- es])

---------------------------------------------------------------------
exit :: a -> IO a -> IO a
---------------------------------------------------------------------
exit def act = catch act $ \(e :: Error) -> do
  putDocLn $ vcat ["Unexpected Errors!", pprint e]
  return def

putDocLn :: Doc -> IO ()
putDocLn = putStrLn . render
---------------------------------------------------------------------
-- | Result ---------------------------------------------------------
---------------------------------------------------------------------

data FixResult a = Crash [a] String
                 | Safe
                 | Unsafe ![a]
                   deriving (Data, Typeable, Foldable, Traversable, Show, Generic)

instance (NFData a) => NFData (FixResult a)

instance Eq a => Eq (FixResult a) where
  Crash xs _ == Crash ys _        = xs == ys
  Unsafe xs == Unsafe ys          = xs == ys
  Safe      == Safe               = True
  _         == _                  = False

instance Monoid (FixResult a) where
  mempty                          = Safe
  mappend Safe x                  = x
  mappend x Safe                  = x
  mappend _ c@(Crash _ _)         = c
  mappend c@(Crash _ _) _         = c
  mappend (Unsafe xs) (Unsafe ys) = Unsafe (xs ++ ys)

instance Functor FixResult where
  fmap f (Crash xs msg)   = Crash (f <$> xs) msg
  fmap f (Unsafe xs)      = Unsafe (f <$> xs)
  fmap _ Safe             = Safe

resultDoc :: (Fixpoint a) => FixResult a -> Doc
resultDoc Safe             = text "Safe"
resultDoc (Crash xs msg)   = vcat $ text ("Crash!: " ++ msg) : ((("CRASH:" <+>) . toFix) <$> xs)
resultDoc (Unsafe xs)      = vcat $ text "Unsafe:"           : ((("WARNING:" <+>) . toFix) <$> xs)

colorResult :: FixResult a -> Moods
colorResult (Safe)      = Happy
colorResult (Unsafe _)  = Angry
colorResult (_)         = Sad

---------------------------------------------------------------------
-- | Catalogue of Errors --------------------------------------------
---------------------------------------------------------------------

errFreeVarInQual :: (PPrint q, Loc q, PPrint x) => q -> x -> Error
errFreeVarInQual q x = err sp $ vcat [ "Qualifier with free vars"
                                     , pprint q
                                     , pprint x ]
  where
    sp               = srcSpan q

errFreeVarInConstraint :: (PPrint a) => (Integer, a) -> Error
errFreeVarInConstraint (i, ss) = err dummySpan $
  vcat [ "Constraint with free vars"
       , pprint i
       , pprint ss
       , "Try using the --prune-unsorted flag"
       ]

errIllScopedKVar :: (PPrint k, PPrint bs) => (k, Integer, Integer, bs) -> Error
errIllScopedKVar (k, inId, outId, xs) = err dummySpan $
  vcat [ "Ill-scoped KVar" <+> pprint k
       , "Missing common binders at def" <+> pprint inId <+> "and use" <+> pprint outId
       , pprint xs
       ]
