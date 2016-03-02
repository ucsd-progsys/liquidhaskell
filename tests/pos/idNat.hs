module IdNat where 

{-@ nat :: Nat @-}
nat :: Int
nat = id 0 -- (id (id (id (id 0))))
