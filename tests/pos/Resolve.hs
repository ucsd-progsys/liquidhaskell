module Resolve where

import qualified ResolveA as RA
import qualified ResolveB as RB


{-@ x :: {v:RB.Bar | ((v = RB.B) && (NotA v))} @-}
x = RB.B

zebra :: Int
zebra = 12 
