{-@ LIQUID "--expect-any-error" @-}

module T745 where

foo :: () -> ()
foo () = foo ()
