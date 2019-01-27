module A where 

    import B 
    
    a :: Eq a => B a -> Bool 
    a (B x y) = x == y 