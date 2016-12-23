module Books where

data Customer = Vip | Reg deriving (Eq)

{-@ inline foo @-}
foo :: Customer -> Bool
foo c = c == Vip
