-- | test reflection of private variables of imported modules

{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--reflection" @-}

module ReflExt03A where

import ReflExt03B

{-@ reflect f @-}
{-@ private-reflect ReflExt03B.myAdd @-}

-- 3 * 2 + 2 = 8
{-@ lemma :: {f 3 2 = 8} @-}
lemma = ()

{-@ lemma2 :: { ReflExt03B.myAdd 3 2 = 5} @-}
lemma2 = ()
