module Dummy (foo) where

data Pair a b = Pair a b

{-@ foo :: Nat -> Nat -> Nat -> Nat @-}
foo :: Int -> Int -> Int -> Int
foo a b c = x + y + z 
  where
    Pair x (Pair y z) = runList $ do xiggety <- return (a + 1)
                                     yogurt  <- return (b + 1)
                                     zagbert <- return (c + 1)
                                     return  (Pair xiggety (Pair yogurt zagbert))

runList :: [a] -> a
runList = undefined
