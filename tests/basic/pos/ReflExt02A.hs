-- | test reflection away from another imported module (ReflExt02B)
-- | By the way, check that what happens when there is a function named the same as the imported one.
-- | Also, we see that qualified form can be used for reflection of public variables from foreign modules.

{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--reflection" @-}

module ReflExt02A where

import ReflExt02B

{-@ reflect ReflExt02B.myAdd @-}

{-@ reflect myAdd @-}
myAdd :: Int
myAdd = 12

-- 3 + 2 + 1 = 6
{-@ lemma :: {ReflExt02B.myAdd 3 2 = 6 } @-}
lemma = ()