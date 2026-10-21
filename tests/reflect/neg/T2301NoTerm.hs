{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination-check" @-}

-- Disabling the termination checker for the whole file must not disable
-- refinement checking: the contradictory refinement of the reflected
-- non-terminating definition is still rejected. See
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2301

module T2301NoTerm where

data L a = Nil | Cons a (L a)

{-@ reflect listSum @-}
{-@ listSum :: L Nat -> Nat @-}
listSum :: L Int -> Int
listSum Nil         = 0
listSum (Cons h t)  = h + listSum t

{-@ reflect ones @-}
{-@ ones :: {l:L Nat | listSum l < 5} @-}
ones :: L Int
ones = Cons 1 ones
