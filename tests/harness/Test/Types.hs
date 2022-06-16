{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.Types where

import Data.Text (Text)

type TestGroupName = Text

data Options = Options
  { testGroups :: [TestGroupName]
  , showAll :: Bool
  }
  deriving stock (Eq, Ord, Show)
