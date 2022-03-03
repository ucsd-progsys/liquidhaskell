module Client2Lib where 

    {-@ reflect cProp @-}
    
    cProp :: Eq a => a -> a -> Bool 
    cProp x y = x == y 


