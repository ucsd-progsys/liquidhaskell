{-@ LIQUID "--expect-error-containing=Unknown type constructor `Zoog`" @-}
module BadData0 where

data Zog = Z Int
{-@ data Zoog = Z { mkZ :: Nat } @-}

frog = Z (0 - 5)
