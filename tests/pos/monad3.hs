module Foo where

import Language.Haskell.Liquid.Prelude


gpp z = do x <- z
           return $ liquidAssert (x >= 0) (x + 1)


xs, ys, zs :: [Int]
xs = [0..]
ys = gpp xs
zs = gpp ys
