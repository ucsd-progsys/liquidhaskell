{-@ LIQUID "--expect-any-error" @-}
module T1288 where

{-@ measure foo @-}
foo :: () -> Int
foo _ = 10

{-@ blub :: {v:Int | v = 100} @-}
blub = foo ()
