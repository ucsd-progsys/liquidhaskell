module Niki where

import Language.Haskell.Liquid.Prelude

data Pair a b = P a b

foo = chk (P (0) (1))

chk (P x y) = assert (x <= y)

