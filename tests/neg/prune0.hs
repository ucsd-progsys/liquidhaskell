{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Prune where

import Prelude hiding (read, length)
import Control.Monad.Primitive
import Data.Vector.Generic.Mutable

----------------------------------------------------------------------------
-- LIQUID Specifications ---------------------------------------------------
----------------------------------------------------------------------------

-- | Vector Size Measure

{-@ measure vsize :: forall a. a -> Int @-}

-- | Vector Type Aliases
{-@ type      OkIdx X     = {v:Nat | v < (vsize X)} @-}

-- | Assumed Types for Vector

{-@ unsafeRead  
      :: (PrimMonad m, MVector v a) 
      => xorp:(v (PrimState m) a) 
      -> (OkIdx xorp) 
      -> m a       
  @-}

yuck xanadu i = if (i > 0) then unsafeRead xanadu i else undefined






















