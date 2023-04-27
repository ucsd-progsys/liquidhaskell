{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Storable_LHAssumptions where

import GHC.Ptr_LHAssumptions()
import Foreign.Storable

{-@
predicate PValid P N         = ((0 <= N) && (N < (plen P)))

assume Foreign.Storable.poke        :: (Foreign.Storable.Storable a)
                             => {v: (GHC.Ptr.Ptr a) | 0 < (plen v)}
                             -> a
                             -> (GHC.Types.IO ())

assume Foreign.Storable.peek        :: (Foreign.Storable.Storable a)
                             => p:{v: (GHC.Ptr.Ptr a) | 0 < (plen v)}
                             -> (GHC.Types.IO {v:a | v = (deref p)})

assume Foreign.Storable.peekByteOff :: (Foreign.Storable.Storable a)
                             => forall b. p:(GHC.Ptr.Ptr b)
                             -> {v:GHC.Types.Int | (PValid p v)}
                             -> (GHC.Types.IO a)

assume Foreign.Storable.pokeByteOff :: (Foreign.Storable.Storable a)
                             => forall b. p:(GHC.Ptr.Ptr b)
                             -> {v:GHC.Types.Int | (PValid p v)}
                             -> a
                             -> GHC.Types.IO ()
@-}
