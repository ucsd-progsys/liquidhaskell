module spec GHC.Base where

import GHC.Prim
import GHC.Classes
import GHC.Types
import GHC.Err  

assume $         :: (x:a -> b) -> a -> b
assume map       :: (x:a -> b) -> xs:[a] -> {v: [b] | len(v) = len(xs)}
assume id        :: x:a -> {v:a | v = x}
