module Resolve where

import qualified ResolveLib as RA
import qualified ResolveLibLib as RB


{-@ x :: {v:RB.Bar | ((v = RB.B) && (NotA v))} @-}
x = RB.B

zebra :: Int
zebra = 12 
