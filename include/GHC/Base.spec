module spec GHC.Base where

import GHC.Prim
import GHC.Classes
import GHC.Types
import GHC.Err  

measure len :: forall a. [a] -> GHC.Types.Int
len ([])     = 0
len (y:ys)   = 1 + len(ys)


invariant {v: [a] | len(v) >= 0 } 


assume $         :: (x:a -> b) -> a -> b
assume map       :: (x:a -> b) -> xs:[a] -> {v: [b] | len(v) = len(xs)}
assume id        :: x:a -> {v:a | v = x}
