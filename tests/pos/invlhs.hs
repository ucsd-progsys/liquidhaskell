module Foo where

data Bob = B {foo :: Int}
{-@ data Bob = B {foo :: Int} @-}

{-@ foo :: x:Bob -> {v:Int | v = foo x} @-}

{-@ invariant {v:Bob | foo v == 10} @-}

mk :: a -> Bob
mk = undefined

{-@ propFAIL :: {v:_ | foo v = 10} @-}
propFAIL = mk ()

{-@ propOK :: {v:_ | foo v = 10} @-}
propOK = let z = mk () in z 


