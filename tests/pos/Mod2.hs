module Mod2 where

import qualified Mod1 as M

{-@ inc :: x:M.Goo -> {v: M.Goo | (myg v) > (myg x)} @-}
inc (M.G x) = M.G (x + 1)

