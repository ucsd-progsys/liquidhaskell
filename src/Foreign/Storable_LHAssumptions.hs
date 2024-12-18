{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Storable_LHAssumptions where

import GHC.Ptr_LHAssumptions()
import Foreign.Storable
import GHC.Ptr

{-@
predicate PValid P N         = ((0 <= N) && (N < (plen P)))

assume poke        :: (Storable a)
                             => {v: (Ptr a) | 0 < (plen v)}
                             -> a
                             -> (IO ())

assume peek        :: (Storable a)
                             => p:{v: (Ptr a) | 0 < (plen v)}
                             -> (IO {v:a | v = (deref p)})

assume peekByteOff :: (Storable a)
                             => forall b. p:(Ptr b)
                             -> {v:Int | (PValid p v)}
                             -> (IO a)

assume pokeByteOff :: (Storable a)
                             => forall b. p:(Ptr b)
                             -> {v:Int | (PValid p v)}
                             -> a
                             -> IO ()
@-}
