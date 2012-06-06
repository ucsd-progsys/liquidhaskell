module Meas where

import Language.Haskell.Liquid.Prelude

--{-# ANN module "spec   $LIQUIDHS/List.spec" #-}
--{-# ANN module "hquals $LIQUIDHS/List.hquals" #-}

mylen :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs

{-
zs :: [Int]
zs = [1..100]

n  = mylen zs

-}
