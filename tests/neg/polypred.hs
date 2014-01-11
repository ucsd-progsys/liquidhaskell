module Concat () where

import Language.Haskell.Liquid.Prelude

prop :: Int -> Bool
prop x = liquidAssertB (x == 0)

foo :: a -> Int
foo longVarName = choose 20 

-- propUNSAFE = prop (foo "ker")
propSAFE = prop (foo id)

