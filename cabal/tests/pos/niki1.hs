module Niki where

import Language.Haskell.Liquid.Prelude

data Pair a = P a 

zero  = (0 :: Int)
pzero = P zero
foo   = chk pzero

chk :: Pair Int -> Bool
chk (P x) = assert (0 <= x)

