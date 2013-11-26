-- |
-- Module      : Data.Vector.Storable.Internal
-- Copyright   : (c) Roman Leshchinskiy 2009-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Ugly internal utility functions for implementing 'Storable'-based vectors.
--

module Data.Vector.Storable.Internal (
  getPtr, setPtr, updPtr
) where

import Control.Monad.Primitive ( unsafeInlineIO )
import Foreign.Storable
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Marshal.Array ( advancePtr )
import GHC.Base         ( quotInt )
import GHC.ForeignPtr   ( ForeignPtr(..) )
import GHC.Ptr          ( Ptr(..) )

getPtr :: ForeignPtr a -> Ptr a
{-# INLINE getPtr #-}
getPtr (ForeignPtr addr _) = Ptr addr

setPtr :: ForeignPtr a -> Ptr a -> ForeignPtr a
{-# INLINE setPtr #-}
setPtr (ForeignPtr _ c) (Ptr addr) = ForeignPtr addr c

updPtr :: (Ptr a -> Ptr a) -> ForeignPtr a -> ForeignPtr a
{-# INLINE updPtr #-}
updPtr f (ForeignPtr p c) = case f (Ptr p) of { Ptr q -> ForeignPtr q c }

