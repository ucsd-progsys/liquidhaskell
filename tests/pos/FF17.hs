{-# LANGUAGE DataKinds #-}
{-@ LIQUID "--smtsolver=cvc5"  @-}

module FF17 where

import Language.Haskell.Liquid.FinField

-- instantiate FFld for a specific prime value of 17
data FF17 = FF17 { toFFld :: FFld 17 }
{-@ embed FF17 as (FFld_t 17) @-}

{-@ assume val :: n : Integer -> {v:FF17 | v = FF_val n} @-}
{-@ define val    n                          = (FF_val n) @-}
val :: Integer -> FF17
val n = FF17 (FFld (n `mod` 17))

{-@ assume add :: x : FF17 -> y : FF17 -> {v:FF17 | v = FF_add x y} @-}
{-@ define add    x           y                      = (FF_add x y) @-}
add :: FF17 -> FF17 -> FF17
add x y = FF17 (FFld (ffToInteger (toFFld x) + ffToInteger (toFFld y) `mod` 17))

{-@ assume mul :: x : FF17 -> y : FF17 -> {v:FF17 | v = FF_mul x y} @-}
{-@ define mul    x           y                      = (FF_mul x y) @-}
mul :: FF17 -> FF17 -> FF17
mul x y = FF17 (FFld (ffToInteger (toFFld x) * ffToInteger (toFFld y) `mod` 17))

-- tests

-- The FFld_t LF sort is parametric in its prime value, meaning we must
-- explicitly specify the concrete type in the refinement so the unifier
-- can properly resolve this value.

{-@ thm1 :: { v : FF17 | v = val 6} -> { add v (val 7) == val 13 } @-}
thm1 :: FF17 -> ()
thm1 _ = ()

{-@ thm2 :: { v : FF17 | v = val 9} -> { add v (val 9) == val 1 } @-}
thm2 :: FF17 -> ()
thm2 _ = ()

{-@ thm3 :: { v : FF17 | v = val 3} -> { mul v (val 7) == val 4 } @-}
thm3 :: FF17 -> ()
thm3 _ = ()
