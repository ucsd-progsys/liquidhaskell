module Pair where 

import Language.Haskell.Liquid.Prelude 

data Pair a b = P a b


incr x = P x (P True (x+1))
chk (P x (P z y)) = assert (x <y) 
prop  = chk $ incr n
  where n = choose 0
