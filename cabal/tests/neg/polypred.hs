module Concat where

import Language.Haskell.Liquid.Prelude

prop :: Int -> Bool
prop x = assert (x == 0)

foo :: a -> Int
foo f = choose 0 

-- propUNSAFE = prop (foo "ker")
propSAFE = prop (foo id)

