

-- LH should complain: "Unknown field `goober` in refined definition of `Foo`"

data Foo = F Int 

{-@ data Foo = F { goober :: Int } @-}

