module Vec0 () where

import Language.Haskell.Liquid.Prelude -- hiding (copyList)

copyList zs = zs

xs    = [1] :: [Int]
ys    = copyList xs
jhala = head ys
prop0 = crash (0 == 1) 
