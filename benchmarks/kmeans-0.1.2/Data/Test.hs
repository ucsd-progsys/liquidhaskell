module Test where

import Language.Haskell.Liquid.Prelude


-- RIGHT SPEC{-# ANN foo "x:Int -> y:{v:Int | v = x} -> Bool" #-}
-- {-# ANN foo "Int -> Int -> Bool" #-}
-- {-# ANN foo "x:Int -> y:Int -> Bool" #-}
foo :: Int -> Int -> Bool
foo x y = assert (x == y) 

--z  = foo n1 n1
--       where n1 = choose 0




