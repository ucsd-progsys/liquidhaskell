module B where

import A

data Exp = Lam Ty

{-@ measure measureExp @-}
measureExp :: Exp -> Int
measureExp _ = 10
