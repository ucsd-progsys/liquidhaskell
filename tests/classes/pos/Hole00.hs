
-- This test checks that we resolve the name `MVector` to 
-- the CLASS defined in the re-exported Data.Vector.Generic.Mutable.Base 
-- NOT to the TyCon inside `Data.Vector.Primitive.Mutable` 

module Hole00 where

import Prelude hiding (read, length)

import           Control.Monad.Primitive
import qualified Data.Vector.Primitive.Mutable as PV
import           Data.Vector.Generic.Mutable

{-@ chimp :: (Monad m, MVector v e) => v (PrimState m) e -> m () @-}
chimp :: (Monad m, MVector v e) => v (PrimState m) e -> m ()
chimp = undefined
