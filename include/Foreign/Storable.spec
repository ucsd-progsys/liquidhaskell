module spec Foreign.Storable where

predicate PValid P N         = ((0 <= N) && (N < (plen P)))   

Foreign.Storable.poke        :: (Foreign.Storable.Storable a) => {v: (GHC.Ptr.Ptr a) | 0 <= (plen v)} -> a -> (IO ())
Foreign.Storable.peek        :: (Foreign.Storable.Storable a) => p:{v: (GHC.Ptr.Ptr a) | 0 <= (plen v)} -> (IO {v:a | v = (deref p)})
Foreign.Storable.peekByteOff :: (Foreign.Storable.Storable a) => forall b. p:(GHC.Ptr.Ptr b) -> {v:Int | (PValid p v)} -> (IO a)
Foreign.Storable.pokeByteOff :: (Foreign.Storable.Storable a) => forall b. p:(GHC.Ptr.Ptr b) -> {v:Int | (PValid p v)} -> a -> IO ()


