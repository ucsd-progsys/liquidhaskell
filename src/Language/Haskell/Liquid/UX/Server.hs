module Language.Haskell.Liquid.UX.Server (getType) where

import           Prelude hiding (error)

-- import           Control.Monad ((<<))
import           Language.Haskell.Liquid.Types (Output(..))
import qualified Language.Haskell.Liquid.UX.ACSS as A
import           Text.PrettyPrint.HughesPJ    hiding (Mode)
import           Language.Fixpoint.Utils.Files
import           System.Directory
import           Data.Time.Clock (UTCTime)
import qualified Control.Exception as Ex
import           Data.Aeson
import qualified Data.ByteString.Lazy   as B

-- data Time = TimeTodo deriving (Eq, Ord, Show)

getType :: IO (Output Doc) -> FilePath -> Int -> Int -> IO String
getType k srcF line col = do
  act <- action srcF
  case act of
    Reuse    -> getTypeInfo line col <$>       getAnnMap srcF
    Rebuild  -> getTypeInfo line col <$> (k >> getAnnMap srcF)
    NoSource -> return "Missing Source"

--------------------------------------------------------------------------------
-- | How to Get Info
--------------------------------------------------------------------------------

data Action = Rebuild | Reuse | NoSource

action :: FilePath -> IO Action
action srcF = timeAction <$> modificationTime srcF <*> modificationTime jsonF
  where
    jsonF   = extFileName Json srcF

timeAction :: Maybe UTCTime -> Maybe UTCTime -> Action
timeAction (Just srcT) (Just jsonT)
  | srcT < jsonT  = Reuse
timeAction (Just _) _ = Rebuild
timeAction Nothing _  = NoSource

modificationTime :: FilePath -> IO (Maybe UTCTime)
modificationTime f = (Just <$> getModificationTime f) `Ex.catch` handler
  where
    handler :: IOError -> IO (Maybe UTCTime)
    handler = const (return Nothing)

--------------------------------------------------------------------------------

getTypeInfo :: Int -> Int -> Maybe A.AnnMap -> String
getTypeInfo _ _ Nothing     = "ERROR: corrupt annotation info"
getTypeInfo l c (Just info) = error "TODO: getTypeInfo"

getAnnMap :: FilePath -> IO (Maybe A.AnnMap)
getAnnMap srcF = decode <$> B.readFile jsonF
  where
    jsonF      = extFileName Json srcF
