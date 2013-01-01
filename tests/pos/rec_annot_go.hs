module Fixme where

import Language.Haskell.Liquid.Prelude (liquidAssert)

loop :: Int -> Int -> a -> (Int -> a -> a) -> a 
loop lo hi base f = go base lo
  where
    go acc i     
      | i /= hi   = go (f i acc) (i + 1)
      | otherwise = acc

poo = loop 0 10 0 (+)

