module Pair where 

import Language.Haskell.Liquid.Prelude 

data Pair a b = P a b

incr x = P x ((x+1))
chk (P x (y)) = assert (x <y) 
prop  = chk $ incr n
  where n = choose 0

-- 43(ok) -/-> 94 -/-> k_22
incr2 x = P x (P True (x+1))
chk2 (P x w) = 
   case w of (P z y) -> assert (x <y) 
prop2  = chk2 $ incr2 n
  where n = choose 0

