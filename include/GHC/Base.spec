module spec GHC.Base where

import GHC.Prim
import GHC.Classes
import GHC.Types

embed GHC.Types.Int      as int
embed Prop               as bool

measure Prop   :: GHC.Types.Bool -> Prop

measure len :: forall a. [a] -> GHC.Types.Int
len ([])     = 0
len (y:ys)   = 1 + (len ys)

measure null :: forall a. [a] -> Prop
null ([])   = true
null (x:xs) = false

measure fst :: (a,b) -> a
fst (a,b) = a

measure snd :: (a,b) -> b
snd (a,b) = b

invariant {v: [a] | len(v) >= 0 } 
assume map       :: (a -> b) -> xs:[a] -> {v: [b] | len(v) = len(xs)}

assume $         :: (a -> b) -> a -> b
assume id        :: x:a -> {v:a | v = x}


