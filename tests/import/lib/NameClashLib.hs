module NameClashLib where 

data Foo = FooLib Int 

{-@ type FooAlias = {v : Foo | False} @-}
foo :: Foo -> Int 
foo _ = 10
