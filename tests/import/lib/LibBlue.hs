module LibBlue where 

data Thing = ThingBlue Int 

{-@ foo :: Int -> Thing @-}
foo :: Int -> Thing 
foo = ThingBlue 

