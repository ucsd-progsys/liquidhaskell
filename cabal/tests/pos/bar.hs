module Bar where

import Language.Haskell.Liquid.Prelude

prop = let s = (\x -> x + 1)  $ 3 in 
       let s1 = (\x -> x - 1) $ 4 in
       liquidAssert (s > 3 && s1 < 4) 

