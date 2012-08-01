module spec GHC.Base where

import GHC.Prim
import GHC.List
import GHC.Classes
import GHC.Types
import GHC.Err  

-- TODO: assume ($)      :: forall <p :: a -> Bool>. (x: a -> b<p x>) -> y:a -> b<p y>
assume $         :: (x:a -> b) -> a -> b
assume map       :: (a -> b) -> xs:[a] -> {v: [b] | len(v) = len(xs)}
assume id        :: x:a -> {v:a | v = x}
