{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module T1604 where

data Val = V { val :: Int }
{-@ data Val = V { val :: Int } @-}
{-@ type ValN N = {v:Val | val v == N} @-}

{-@ reflect ex1 @-}
{-@ ex1 :: ValN 5 @-}
ex1 :: Val
ex1 = V 4


{-@ test1 :: {v:Bool | v} @-}
test1 = val ex1 == 6

{-@ test2 :: () -> {v:() | val ex1 == 6} @-}
test2 () = ()

{-@ test3 :: () -> {v:() | 1 == 2} @-}
test3 () = ()
