module Wrap0 where

import Language.Haskell.Liquid.Prelude (liquidAssertB)

{-@ data Coo <p :: Int -> Bool> = C (z :: Int <p>) @-}
data Coo = C Int

prop x (C y) = liquidAssertB (x == y)

{-@ assert flibberty :: Int -> Bool @-}
flibberty x = prop x (C x)
