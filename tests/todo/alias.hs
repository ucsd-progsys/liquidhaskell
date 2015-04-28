module Foo where

{-@ type Pos = {v:Int | 0 < v} @-}
type Pos = Int

-- If I add the explicit @-annotation then of course liquid marks this program
-- unsafe, but it would be nice if we could get the same result (i.e. unsafe)
-- directly by using the Haskell type. (This would be a step towards
-- @spindakin's summer project using TF).

incr   :: Pos -> Pos
incr x = x - 1
