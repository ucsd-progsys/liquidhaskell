module IdNat where 

{-@ nat :: Nat @-}
nat :: Int
nat = idd 0 

idd :: a -> a
idd = undefined 
