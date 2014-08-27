module Pair () where 

{-@ LIQUID "--no-termination" @-}
import Language.Haskell.Liquid.Prelude 

data Pair a b = P a b


incr x = (x, x+1)
chk (x, y) = liquidAssertB (x <y) 
prop  = chk $ incr n
  where n = choose 0

incr2 x = (x, True, x+1)
chk2 (x, _, y) = liquidAssertB (x <y) 
prop2  = chk2 $ incr2 n
  where n = choose 0

incr3 x = (x, (True, (0, x+1)))
chk3 (x, (_, (_, y))) = liquidAssertB (x <y) 
prop3  = chk3 $ incr3 n
  where n = choose 0
