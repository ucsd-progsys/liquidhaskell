module Fixme0 where

import Language.Haskell.Liquid.Prelude

data Map k a = Tip

{-@ assert insert :: (Ord k) => x:k -> v:a -> Map {v: k | v >= x} a @-}
insert            :: (Ord k) => k -> a -> Map k a
insert kx x       = Tip
