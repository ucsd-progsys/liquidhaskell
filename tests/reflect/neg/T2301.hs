{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- The contradictory refinement of a reflected, non-terminating definition
-- must be rejected. Reflecting @ones@ used to make the check vacuous, see
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2301

module T2301 where

data L a = Nil | Cons a (L a)

{-@ reflect listSum @-}
{-@ listSum :: L Nat -> Nat @-}
listSum :: L Int -> Int
listSum Nil         = 0
listSum (Cons h t)  = h + listSum t

{-@ lazy ones @-}
{-@ reflect ones @-}
{-@ ones :: {l:L Nat | listSum l < 5} @-}
ones :: L Int
ones = Cons 1 ones
