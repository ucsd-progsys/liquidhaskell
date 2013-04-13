{--! run liquid with nofalse -}

module HaskellElephant where 

{-@ f :: a -> {v : b | false} @-}
f x = f x
 
{-@ error' :: {v: String | false } -> a  @-}
error'     :: String -> a
error'     = error
 
{-@ lAssert :: {v:Bool | Prop(v)} -> a -> a @-}
lAssert :: Bool -> a -> a
lAssert True x = x
lAssert False _ = error' "lAssert failure"
 
main = print ((\_ x -> lAssert (x /= 100) x) (f 3) 100)

