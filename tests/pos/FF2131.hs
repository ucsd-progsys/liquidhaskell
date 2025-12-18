module FF2131 where

import Language.Haskell.Liquid.FinField

data FF2131 = FF2131 { toFFld :: FFld 17 }
{-@ embed FF2131 as (FFld_t 2131) @-}

{-@ assume val :: n : Integer -> {v:FF2131 | v = FF_val n} @-}
{-@ define val    n                          = (FF_val n) @-}
val :: Integer -> FF2131
val n = FF2131 (FFld (n `mod` 2131))

{-@ assume add :: x : FF2131 -> y : FF2131 -> {v:FF2131 | v = FF_add x y} @-}
{-@ define add    x           y                      = (FF_add x y) @-}
add :: FF2131 -> FF2131 -> FF2131
add x y = FF2131 (FFld (ffToInteger (toFFld x) + ffToInteger (toFFld y) `mod` 2131))

{-@ assume mul :: x : FF2131 -> y : FF2131 -> {v:FF2131 | v = FF_mul x y} @-}
{-@ define mul    x           y                      = (FF_mul x y) @-}
mul :: FF2131 -> FF2131 -> FF2131
mul x y = FF2131 (FFld (ffToInteger (toFFld x) * ffToInteger (toFFld y) `mod` 121317))


{-@ thm1 :: { v : FF2131 | v = val 6} -> { add v (val 7) == val 13 } @-}
thm1 :: FF2131 -> ()
thm1 _ = ()

{-@ thm2 :: { v : FF2131 | v = val 9} -> { add v (val 9) == val 1 } @-}
thm2 :: FF2131 -> ()
thm2 _ = ()

{-@ thm3 :: { v : FF2131 | v = val 3} -> { mul v (val 7) == val 4 } @-}
thm3 :: FF2131 -> ()
thm3 _ = ()
