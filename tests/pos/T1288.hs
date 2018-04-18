
{-@ measure foo @-}
foo :: () -> Int
foo _ = 10

{-@ blub :: {v:Int | v = 10} @-}
blub = foo ()
