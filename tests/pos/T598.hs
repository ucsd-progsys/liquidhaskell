{-# LANGUAGE DeriveGeneric #-}

module T598 where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData(..))

data Point = Point
    { x :: Int
    } deriving (Generic)

instance NFData Point
