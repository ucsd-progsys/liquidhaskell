module ListDemo where

data List a = E | (:::) { h :: a, t :: List a }

infixr  9 ::: 

{-@ countUp :: n:Int -> List Int @-}
countUp n  = n ::: countUp (n + 1)










