module IdNat where 

{-@ nat :: Nat @-}
nat :: Int
nat = id (id (id (id (id 0))))
