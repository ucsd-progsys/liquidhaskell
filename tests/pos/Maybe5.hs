module Maybe5 where

import Data.Maybe


{-@ foo :: {x:_ | isJust x} -> a @-}
foo :: Maybe a -> a
foo x = fromJust x
