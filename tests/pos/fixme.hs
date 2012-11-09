module Pair where 

import Language.Haskell.Liquid.Prelude 
 
incr3 x = (x, (True, (0, x+1)))
chk3 (x, (_, (_, y))) = liquidAssertB (x < y) 
prop3  = chk3 $ incr3 n
  where n = choose 0
