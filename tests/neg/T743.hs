{-@ LIQUID "--expect-any-error" @-}
module T743 where

{-@ checkNat :: Nat -> Int @-}
checkNat :: Int -> Int
checkNat x = x

unsound :: Int
unsound = checkNat (-1)

data TestBS = TestBS Int deriving (Read)
