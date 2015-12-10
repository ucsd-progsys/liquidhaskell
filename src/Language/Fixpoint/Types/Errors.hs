{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

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
  , catMessage
  , catError
  , catErrors

  -- * Fatal Exit
  , die
  , exit

  -- * Some popular errors
  , errFreeVarInQual
  ) where

import           Control.Exception
import qualified Control.Monad.Error           as E
import           Data.Serialize                (Serialize (..))
import           Data.Generics                 (Data)
import           Data.Typeable
import           Control.DeepSeq
-- import           Data.Hashable
import qualified Data.Binary                   as B
import           GHC.Generics                  (Generic)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Utils.Misc
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
-- import           Debug.Trace

instance Serialize Error
instance (B.Binary a) => B.Binary (FixResult a)

-----------------------------------------------------------------------
-- | A BareBones Error Type -------------------------------------------
-----------------------------------------------------------------------

data Error = Error { errLoc :: SrcSpan
                   , errMsg :: String }
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance PPrint Error where
  pprint (Error l msg) = pprint l <> text (": Error: " ++ msg)

instance Fixpoint Error where
  toFix = pprint

instance Exception Error
instance Exception (FixResult Error)
instance E.Error Error where
  strMsg = Error dummySpan

---------------------------------------------------------------------
catMessage :: Error -> String -> Error
---------------------------------------------------------------------
catMessage e msg = e {errMsg = msg ++ errMsg e}

---------------------------------------------------------------------
catError :: Error -> Error -> Error
---------------------------------------------------------------------
catError e1 e2 = catMessage e1 $ show e2

---------------------------------------------------------------------
catErrors :: ListNE Error -> Error
---------------------------------------------------------------------
catErrors = foldr1 catError

---------------------------------------------------------------------
err :: SrcSpan -> String -> Error
---------------------------------------------------------------------
err = Error

---------------------------------------------------------------------
die :: Error -> a
---------------------------------------------------------------------
die = throw

---------------------------------------------------------------------
exit :: a -> IO a -> IO a
---------------------------------------------------------------------
exit def act = catch act $ \(e :: Error) -> do
  putStrLn $ "Unexpected Error: " ++ showpp e
  return def


---------------------------------------------------------------------
-- | Result ---------------------------------------------------------
---------------------------------------------------------------------

data FixResult a = Crash [a] String
                 | Safe
                 | Unsafe ![a]
                   deriving (Data, Typeable, Show, Generic)

instance (NFData a) => NFData (FixResult a)

resultDoc :: (Fixpoint a) => FixResult a -> Doc
resultDoc Safe             = text "Safe"
resultDoc (Crash xs msg)   = vcat $ text ("Crash!: " ++ msg) : (((text "CRASH:" <+>) . toFix) <$> xs)
resultDoc (Unsafe xs)      = vcat $ text "Unsafe:"           : (((text "WARNING:" <+>) . toFix) <$> xs)

colorResult :: FixResult a -> Moods
colorResult (Safe)      = Happy
colorResult (Unsafe _)  = Angry
colorResult (_)         = Sad

---------------------------------------------------------------------
-- | Catalogue of Errors --------------------------------------------
---------------------------------------------------------------------

errFreeVarInQual  :: (Fixpoint a, Loc a) => a -> Error
errFreeVarInQual q = err sp $ printf "Qualifier with free vars : %s \n" (showFix q)
  where
    sp             = srcSpan q
