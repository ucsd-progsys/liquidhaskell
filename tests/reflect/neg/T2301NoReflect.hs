{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- Comparison without reflection: the contradictory refinement is rejected,
-- as it was before the fix for
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2301

module T2301NoReflect where

data L a = Nil | Cons a (L a)

{-@ reflect listSum @-}
{-@ listSum :: L Nat -> Nat @-}
listSum :: L Int -> Int
listSum Nil         = 0
listSum (Cons h t)  = h + listSum t

{-@ lazy ones @-}
{-@ ones :: {l:L Nat | listSum l < 5} @-}
ones :: L Int
ones = Cons 1 ones
