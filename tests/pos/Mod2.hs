module Mod2 where

import qualified Mod1 as M

import qualified Mod1

{-@ inc :: x:Mod1.Goo -> {v: Mod1.Goo | (myg v) > (myg x)} @-}
inc (M.G x) = M.G (x + 1)

