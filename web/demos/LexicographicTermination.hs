module LexicographicTermination where

import Language.Haskell.Liquid.Prelude (liquidError)

-- | Ackermann Function Terminate?

{-@ Decrease ack 1 2 @-}

{-@ ack :: m:Nat -> n:Nat -> Nat @-}
ack :: Int -> Int -> Int

ack m n
    | m == 0          = n + 1
    | m > 0 && n == 0 = ack (m-1) 1
    | m > 0 && n >  0 = ack (m-1) (ack m (n-1))
    | otherwise       = liquidError "Bad arguments!!!"

-- | Alternative annotation:
{- ack :: m:Nat -> n:Nat -> Nat / [m, n] -}
