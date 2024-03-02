{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Storable_LHAssumptions where

import GHC.Ptr_LHAssumptions()
import Foreign.Storable

{-@
predicate PValid P N         = ((0 <= N) && (N < (plen P)))

assume GHC.Internal.Foreign.Storable.poke        :: (GHC.Internal.Foreign.Storable.Storable a)
                             => {v: (GHC.Internal.Ptr.Ptr a) | 0 < (plen v)}
                             -> a
                             -> (GHC.Types.IO ())

assume GHC.Internal.Foreign.Storable.peek        :: (GHC.Internal.Foreign.Storable.Storable a)
                             => p:{v: (GHC.Internal.Ptr.Ptr a) | 0 < (plen v)}
                             -> (GHC.Types.IO {v:a | v = (deref p)})

assume GHC.Internal.Foreign.Storable.peekByteOff :: (GHC.Internal.Foreign.Storable.Storable a)
                             => forall b. p:(GHC.Internal.Ptr.Ptr b)
                             -> {v:GHC.Types.Int | (PValid p v)}
                             -> (GHC.Types.IO a)

assume GHC.Internal.Foreign.Storable.pokeByteOff :: (GHC.Internal.Foreign.Storable.Storable a)
                             => forall b. p:(GHC.Internal.Ptr.Ptr b)
                             -> {v:GHC.Types.Int | (PValid p v)}
                             -> a
                             -> GHC.Types.IO ()
@-}
