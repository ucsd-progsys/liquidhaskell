{-@ LIQUID "--exactdc" @-}

module A where 

data Foo a b= Foo {fooA :: a, fooB :: b} 
{-@ data Foo a b = Foo {fooA :: a, fooB :: b} @-} 