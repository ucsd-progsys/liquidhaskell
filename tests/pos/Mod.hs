module Mod where

import qualified ModLib as M

{-@ inc :: x:M.Goo -> {v: M.Goo | myg v > myg x} @-}
inc (M.G x) = M.G (x + 1)

