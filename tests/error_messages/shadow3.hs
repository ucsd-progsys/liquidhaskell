module Shadow where 

data Poo = Poo Int 

{-@ measure unPoo :: Poo -> Int 
    unPoo (Poo n) = n 
  @-}

{-@ test :: p:Poo -> {v:Int | v = unPoo p} @-}
test :: Poo -> Int 
test (Poo n) = n 

flinkertyPoz = unPoo 
  where 
    unPoo :: Int
    unPoo = 12 
