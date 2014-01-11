module Bar () where

import Language.Haskell.Liquid.Prelude

prop = let s = (\x -> x + 1)  $ 3 in 
       let s1 = (\x -> x - 1) $ 4 in
       liquidAssertB (s > 3 && s1 < 4) 

