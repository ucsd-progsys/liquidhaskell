{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--interpreter" @-}

module Fib where


{-@ thm10 :: () -> {fib 10 = 55} @-}
thm10 :: () -> ()
thm10 _ = ()

{-@ thm7 :: () -> {fib 7 = 13} @-}
thm7 :: () -> ()
thm7 _ = ()


{-@ reflect fib @-}
fib :: Int -> Int 
fib 0 = 0 
fib 1 = 1 
fib i = fib (i-1) + fib (i-2)
