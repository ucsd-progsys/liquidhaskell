module Meas () where

import Language.Haskell.Liquid.Prelude

mylen :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs

{-
zs :: [Int]
zs = [1..100]

n  = mylen zs

-}
