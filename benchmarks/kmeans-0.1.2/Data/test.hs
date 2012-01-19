module Test where

import Language.Haskell.Liquid.Prelude

foo :: Int -> Int -> Bool
foo x y = assert (x == y) 

--z  = foo n1 n1
--       where n1 = choose 0




