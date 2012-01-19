module Foldr where

import Language.Haskell.Liquid.Prelude
import Data.List (foldl')

foo ::  a -> b -> c -> d
foo = \_ _ _ -> crash False 

bar ::  p -> [(q, r)] -> p
bar = foldr (\(key, value) -> foo key value)


