module Dummy (foo) where

import GHC.ST (ST, runST)

data Pair a b = Pair a b

{-@ foo :: Int -> Nat @-}
foo :: Int -> Int
foo b = y + z
  where
    (Pair y z) = runST $ do yogurt      <- undefined
                            (zag, zink) <- thing2 yogurt
                            oink        <- thing1 zag
                            return  (Pair oink zink)

{-@ thing2 :: Int -> ST s (Int, Int) @-}
thing2 :: Int -> ST s (Int, Int)
thing2 = undefined

{-@ thing1 :: Int -> ST s Int @-}
thing1 :: Int -> ST s Int
thing1 = undefined
