-- | Check the behavior of reflection from interface files with user-defined decreasing sizes

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module ReflExt07A where

import ReflExt07B

{-@ reflect leftMostEl @-}

{-@ lemma :: {leftMostEl (Leaf 2) == 2} @-}
lemma = ()