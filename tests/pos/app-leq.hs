module AppLeq (main) where

app f x = f x
check x y = assert (x == y)
main a b = app (check (a<=b)) (a<=b)

------------------------------------------------------
{-@ assume liquidAssert :: {v:Bool | v} -> a -> a  @-}
liquidAssert :: Bool -> a -> a
liquidAssert _ x = x

{-@ assert :: {v:Bool | v} -> () @-}
assert x = liquidAssert x ()
