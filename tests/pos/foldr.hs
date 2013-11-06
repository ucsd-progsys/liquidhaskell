module Foldr where

import Language.Haskell.Liquid.Prelude
import Data.List (foldl')

foo ::  a -> b -> c -> d
foo = \_ _ _ -> error "False" 

-- Used to be, which is clearly bogus (and failed after public-top-ing)
-- foo = \_ _ _ -> crash False

bar ::  p -> [(q, r)] -> p
bar = foldr (\(k, v) -> foo k v)
