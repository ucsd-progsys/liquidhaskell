-- | test the error message when doing reflection of foreign functions with data selectors
-- | W/O having specified the `exactdc`/`reflection` flag
{-@ LIQUID "--expect-error-containing=Illegal type specification for `ReflExt02B.calories`" @-}

module ReflExt02A where

--Oh, no, we forgot to add --exactdc/--reflection!

import ReflExt02B

{-@ reflect calories @-}
