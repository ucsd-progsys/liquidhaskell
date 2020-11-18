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
{-# LANGUAGE ViewPatterns              #-}

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
  , resultExit

  -- * Error Type
  , Error, Error1

  -- * Constructor
  , err

  -- * Accessors
  , errLoc
  , errMsg
  , errs

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

import           System.Exit                        (ExitCode (..))
import           Control.Exception
import           Data.Serialize                (Serialize (..))
import           Data.Aeson                    hiding (Error, Result)
import           Data.Generics                 (Data)
import           Data.Typeable
#if !MIN_VERSION_base(4,14,0)
import           Data.Semigroup                (Semigroup (..))
#endif

import           Control.DeepSeq
-- import           Data.Hashable
import qualified Data.Binary                   as B
import           GHC.Generics                  (Generic)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Solver.Stats as Solver
import           Text.PrettyPrint.HughesPJ.Compat
-- import           Text.Printf
import           Data.Function (on)

-- import           Debug.Trace

import qualified Text.PrettyPrint.Annotated.HughesPJ as Ann

deriving instance Generic (Ann.AnnotDetails a)
instance Serialize a => Serialize (Ann.AnnotDetails a)
instance Serialize a => Serialize (Ann.Doc a)

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


errs :: Error -> [Error1]
errs (Error es) = es 

data Error1 = Error1
  { errLoc :: SrcSpan
  , errMsg :: Doc
  } deriving (Eq, Show, Typeable, Generic)

instance Ord Error1 where
  compare = compare `on` errLoc

instance PPrint Error1 where
  pprintTidy k (Error1 l msg) = (pprintTidy k l <-> ": Error")
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
                 | Safe Solver.Stats
                 -- ^ The 'Solver' statistics, which include also the constraints /actually/
                 -- checked. A program will be \"trivially safe\" in case this
                 -- number is 0.
                 | Unsafe Solver.Stats ![a]
                   deriving (Data, Typeable, Foldable, Traversable, Show, Generic)

instance (NFData a) => NFData (FixResult a)

instance Eq a => Eq (FixResult a) where
  Crash xs _   == Crash ys _         = xs == ys
  Unsafe s1 xs == Unsafe s2 ys       = xs == ys && s1 == s2 
  Safe s1      == Safe s2            = s1 == s2
  _            == _                  = False

instance Semigroup (FixResult a) where
  Safe s1        <> Safe s2        = Safe (s1 <> s2)
  Safe _         <> x              = x
  x              <> Safe _         = x
  _              <> c@(Crash{})    = c
  c@(Crash{})    <> _              = c
  (Unsafe s1 xs) <> (Unsafe s2 ys) = Unsafe (s1 <> s2) (xs ++ ys)

instance Monoid (FixResult a) where
  mempty  = Safe mempty
  mappend = (<>)

instance Functor FixResult where
  fmap f (Crash xs msg)   = Crash (f <$> xs) msg
  fmap f (Unsafe s xs)    = Unsafe s (f <$> xs)
  fmap _ (Safe stats)     = Safe stats

-- instance (ToJSON a) => ToJSON (FixResult a) where
--   toJSON (Safe _ )      = object [ "result"  .= String "safe"   ]

--   toJSON (Unsafe _ ts)  = object [ "result"  .= String "unsafe" 
--                                  , "tags"    .= toJSON ts
--                                  ]
--   toJSON (Crash ts msg) = object [ "result"  .= String "crash"
--                                  , "message" .= msg 
--                                  , "tags"    .= toJSON ts
--                                  ]

instance (ToJSON a) => ToJSON (FixResult a) where
  toJSON = genericToJSON defaultOptions
  toEncoding = genericToEncoding defaultOptions

resultDoc :: (Fixpoint a) => FixResult a -> Doc
resultDoc (Safe stats)     = text "Safe (" <+> text (show $ Solver.checked stats) <+> " constraints checked)" 
resultDoc (Crash xs msg)   = vcat $ text ("Crash!: " ++ msg) : ((("CRASH:" <+>) . toFix) <$> xs)
resultDoc (Unsafe _ xs)    = vcat $ text "Unsafe:"           : ((("WARNING:" <+>) . toFix) <$> xs)

instance (Fixpoint a) => PPrint (FixResult a) where
  pprintTidy _ = resultDoc

colorResult :: FixResult a -> Moods
colorResult (Safe (Solver.totalWork -> 0)) = Wary
colorResult (Safe _)                       = Happy
colorResult (Unsafe _ _)                   = Angry
colorResult (_)                            = Sad

resultExit :: FixResult a -> ExitCode
resultExit (Safe _stats) = ExitSuccess
resultExit _             = ExitFailure 1

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
