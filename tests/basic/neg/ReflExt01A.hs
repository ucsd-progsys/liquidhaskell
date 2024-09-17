-- | test reflection away from the source, when the unfoldings are not available
{-@ LIQUID "--expect-error-containing=Symbol exists but is not defined in the current file, and no unfolding is available in the interface files" @-}
{-@ LIQUID "--reflection" @-}

module ReflExt01A where

import ReflExt01B

{-@ reflect f @-}