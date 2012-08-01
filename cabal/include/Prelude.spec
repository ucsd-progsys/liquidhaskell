module spec Prelude where

import GHC.Base
import GHC.Num
--import GHC.Real
--import GHC.List

assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}
