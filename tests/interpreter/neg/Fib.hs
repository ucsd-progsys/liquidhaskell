{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--interpreter" @-}

module Fib where


{-@ thm :: () -> {fib 7 = 24} @-}
thm :: () -> ()
thm _ = ()

{-@ reflect fib @-}
fib :: Int -> Int 
fib 0 = 0 
fib 1 = 1 
fib i = fib (i-1) + fib (i-2)
