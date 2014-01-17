module Fixme () where

data F a b c = F (Int -> b -> c)
{- data F a b c = F (x::(Int -> b -> c)) @-}


{-@ bar :: F {v:Int| v >= 0} b c @-}
bar :: F Int b c
bar = undefined


{-@ foo :: F {v:Int| v >= 0} b c  -> Int @-}
foo :: F Int b c -> Int
foo = undefined

{-@ hoo :: Int @-}
hoo = foo bar
