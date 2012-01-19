module Vec0 where

import LiquidPrelude

xs    = [1] :: [Int]
ys    = copyList xs
jhala = head ys
prop0 = crash (0 == 1) 
