module Resolve where

import qualified ResolveALib as RA
import qualified ResolveBLib as RB

{-@ x :: {v:RB.Bar | ((v = RB.B) && (NotA v))} @-}
x = RB.B

zebra :: Int
zebra = 12 
