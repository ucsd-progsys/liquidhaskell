module Sumk () where

import Language.Haskell.Liquid.Prelude

m   = choose 0
bot = choose 0

dsum ranjit jhala k =
  if (ranjit `leq` 0)
    then k jhala 
    else dsum (ranjit `minus` 1) (ranjit `plus` jhala) k

prop0 = dsum m bot (\x -> liquidAssertB ((m `plus` bot) `leq` x))

prop1 = liquidAssertB (1 `leq` 0)

