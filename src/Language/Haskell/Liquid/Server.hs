module Language.Haskell.Liquid.Server (getType) where

-- import           Control.Monad ((<<))
import           Language.Haskell.Liquid.Types (Output(..))
import qualified Language.Haskell.Liquid.ACSS as A
import           Text.PrettyPrint.HughesPJ    hiding (Mode)
import           Language.Fixpoint.Files

data Time = TimeTodo deriving (Eq, Ord, Show)

y << x = x >> y

getType :: IO (Output Doc) -> FilePath -> Int -> Int -> IO String
getType act srcF line col = do
  ft  <- modificationTime srcF
  jt  <- modificationTime jsonF
  case action ft jt of
    Reuse    -> getTypeInfo line col <$> getAnnMap jsonF
    Rebuild  -> getTypeInfo line col <$> getAnnMap jsonF << act
    NoSource -> return "Missing Source"
  where
    jsonF    = extFileName Json  srcF

getAnnMap :: FilePath -> IO A.AnnMap
getAnnMap jsonF = error "TODO:reuseInfo"

modificationTime :: FilePath -> IO (Maybe Time)
modificationTime = error "TODO:modificationTime"

data Action = Rebuild | Reuse | NoSource

action :: Maybe Time -> Maybe Time -> Action
action (Just srcT) (Just jsonT)
  | srcT < jsonT  = Reuse
action (Just _) _ = Rebuild
action Nothing _  = NoSource

getTypeInfo :: Int -> Int -> A.AnnMap -> String
getTypeInfo line col info = error "TODO:getTypeInfo"
