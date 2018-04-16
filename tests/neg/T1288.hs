
{-@ measure foo @-}
foo :: () -> Int
foo _ = 10

{-@ blub :: {v:Int | v = 100} @-}
blub = foo ()
