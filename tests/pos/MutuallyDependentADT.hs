module MutuallyDependentADT where

{-@ LIQUID "--exactdc"  @-}

data Pred l 
  = PTerm (Term l)

data Term l 
  = TPred (Pred l)
  | TTerm l

{-@ measure tsize @-}
tsize :: Term l -> Int
{-@ tsize :: Term l -> Nat @-}
tsize (TPred _)            = 0
tsize (TTerm _)            = 0

main :: IO ()
main = pure ()
