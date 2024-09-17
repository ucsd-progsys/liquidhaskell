-- | test that opaque reflection works when unfolding from interface files
-- | and by the way test the fully qualified addressing in reflect annotations

{-@ LIQUID "--reflection" @-}

module ReflExt04A where

import ReflExt04B

{-@ reflect ReflExt04B.f @-}