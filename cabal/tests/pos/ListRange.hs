module ListSort where

import Language.Haskell.Liquid.Prelude

low, high :: Int
low  = choose 0
high = choose 10

range l h = 
  if l <= h then l:(range (l+1) h) else []

chk [] = assert True
chk (x1:xs) = case xs of 
              []       -> assert True
              (x2:xs2) -> assert (x1 <= x2) && chk xs

prop = chk $ range low high
