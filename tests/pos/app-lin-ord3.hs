module AppLeq (main) where

app f x = f x
app3 a f x = a f x
check x y = assert (x == y)
main a b = app3 app (check (4*a+2*b)) (4*a+2*b)

------------------------------------------------------
{-@ assume liquidAssert :: {v:Bool | v} -> a -> a  @-}
liquidAssert :: Bool -> a -> a
liquidAssert _ x = x

{-@ assert :: {v:Bool | v} -> () @-}
assert x = liquidAssert x ()
