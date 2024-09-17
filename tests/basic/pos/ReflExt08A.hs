-- | test reflection of a function that is using a datatype, but not in case split alternatives

{-@ LIQUID "--reflection" @-}

module ReflExt08A where

import ReflExt08B

{-@ reflect fromCal @-}
