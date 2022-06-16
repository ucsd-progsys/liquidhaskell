module Test.Options where

import qualified Data.Text as T
import Test.Groups
import Options.Applicative
import Data.List (intersperse)

data Options = Options
  { testGroups :: [T.Text]
  , showAll :: Bool
  , measureTimings :: Bool
  }
  deriving (Eq, Ord, Show)

options :: Parser Options
options = Options <$>
  many (argument
         (T.pack <$> str)
          (metavar "TESTGROUPNAMES..."
           <> help ("Zero or more of: " <> mconcat (intersperse ", " (T.unpack <$> allTestGroupNames)))))
  <*> switch
        (long "show-all"
         <> help "List all the test types in a manner useful for splitting in Circle CI.")
  <*> switch
        (long "measure-timings"
         <> help "Measure timings when verifying.")

opts :: ParserInfo Options
opts = info (options <**> helper)
  (fullDesc
   <> progDesc "Execute groups of tests.")
