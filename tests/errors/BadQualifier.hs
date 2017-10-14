module RG where
data RGRef a
{-@ measure tv :: RGRef a -> a @-}
{-@ qualif TERMINALVALUE(r:RGRef a): (tv r) @-}


data A
data B

{-@ qualif Foo(x:A, y:B): (x == y) @-}