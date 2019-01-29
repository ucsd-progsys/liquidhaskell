module Client2 where 

    {-@ reflect cProp @-}
    
    cProp :: Eq a => a -> a -> Bool 
    cProp x y = x == y 


