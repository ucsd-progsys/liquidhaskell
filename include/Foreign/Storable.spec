module spec Foreign.Storable where

predicate PValid P N         = ((0 <= N) && (N <= (plen P)))   

Foreign.Storable.poke        :: (Foreign.Storable a) => {v: (Ptr a) | 0 <= (plen v)} -> a -> (IO ())
Foreign.Storable.peek        :: (Foreign.Storable a) => {v: (Ptr a) | 0 <= (plen v)} -> (IO a)
Foreign.Storable.peekByteOff :: (Foreign.Storable a) => forall b. p:(Ptr b) -> {v: Int | (PValid p v) } -> (IO a)
Foreign.Storable.pokeByteOff :: (Foreign.Storable a) => forall b. p:(Ptr b) -> {v:Int | (PValid p v)} -> a -> IO ()


