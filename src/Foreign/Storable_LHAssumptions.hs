{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Storable_LHAssumptions where

import GHC.Ptr_LHAssumptions()
import Foreign.Storable
import GHC.Ptr

{-@
predicate PValid P N         = ((0 <= N) && (N < (plen P)))

assume GHC.Internal.Foreign.Storable.poke        :: (Storable a)
                             => {v: (Ptr a) | 0 < (plen v)}
                             -> a
                             -> (IO ())

assume GHC.Internal.Foreign.Storable.peek        :: (Storable a)
                             => p:{v: (Ptr a) | 0 < (plen v)}
                             -> (IO {v:a | v = (deref p)})

assume GHC.Internal.Foreign.Storable.peekByteOff :: (Storable a)
                             => forall b. p:(Ptr b)
                             -> {v:Int | (PValid p v)}
                             -> (IO a)

assume GHC.Internal.Foreign.Storable.pokeByteOff :: (Storable a)
                             => forall b. p:(Ptr b)
                             -> {v:Int | (PValid p v)}
                             -> a
                             -> IO ()
@-}
