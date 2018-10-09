module LibRed where 

data Thing = ThingRed Int 

{-@ foo :: Int -> Thing @-}
foo :: Int -> Thing 
foo = ThingRed 

