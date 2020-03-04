
module T1461 where

import           Data.List                (sortBy)
import qualified Data.List.NonEmpty       as NE

foo :: NE.NonEmpty a -> Int
foo = NE.length
