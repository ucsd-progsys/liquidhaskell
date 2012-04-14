module Niki where

import Language.Haskell.Liquid.Prelude

data Pair a b = P a b

--bar = P
--foo (P x y) = y

bar = P (0::Int) (1::Int)
foo = chk bar

chk (P x y) = assert (x <= y)
