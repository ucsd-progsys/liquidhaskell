{-@ LIQUID "--exactdc" @-}

module AALib where 

data Foo a b = Foo {fooA :: a, fooB :: b}  |  Bar



{-@ measure isFoo @-}
isFoo :: Foo a b -> Bool
isFoo (Foo _ _)= True 
isFoo Bar = False 
