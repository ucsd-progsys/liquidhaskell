module Zog where

import Language.Haskell.Liquid.Prelude

xs :: [Int]
xs = [1]

poo [] = liquidAssertB False

prop1  = liquidAssertB (poo xs)

{- qualif PosLen(v:[a]): (len v) > 0 @-}

{- zooper :: {v:[a] | (len v) > 0} -> a -}
zooper :: [a] -> a
zooper = undefined
