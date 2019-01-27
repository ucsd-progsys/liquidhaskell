module B where 

    import C
    
    data B a = B {b1 :: a, b2 :: a }
    {-@ data B a = B {b1 :: a, b2 :: {v:a | cProp b1 v } } @-}


