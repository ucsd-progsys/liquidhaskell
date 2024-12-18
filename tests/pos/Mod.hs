module Mod where

import qualified ModLib as M

{-@ inc :: x:M.Goo -> {v: M.Goo | M.myg v > M.myg x} @-}
inc (M.G x) = M.G (x + 1)

