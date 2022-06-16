{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `HoleCrash3.countUp`" @-}
module HoleCrash3 where

data List a = E | (:::) { h :: a, t :: List a }

infixr  9 ::: 

{-@ countUp :: n:Int -> List Int @-}
countUp n  = n ::: countUp (n + 1)










