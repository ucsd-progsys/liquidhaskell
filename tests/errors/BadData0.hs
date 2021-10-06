module BadData0 where

data Zog = Z Int
{-@ data Zoog = Z { mkZ :: Nat } @-}

frog = Z (0 - 5)
