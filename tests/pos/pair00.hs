module Pair () where

{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude

incr z = (x, [x + 1])
  where
    x  = choose z
chk (x, [y]) = liquidAssertB (x < y)
prop  = chk $ incr n
  where
    n = choose 0

incr2 pig = (True, 9, pig, 'o', pig + 1)

chk2 (_, _, cow, _,  dog) = liquidAssertB (cow < dog)

prop2  = chk2 $ incr2 mouse
  where mouse = choose 0

incr3 x = (x, ( (0, x+1)))
chk3 (x, ((_, y))) = liquidAssertB (x < y)
prop3  = chk3 (incr3 n)
 where n = choose 0
