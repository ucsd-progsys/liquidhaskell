{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- Mutually recursive non-terminating CAFs must not slip through the vicious
-- CAF filter: the equations a = Cons 1 b and b = Cons 1 a jointly trivialize
-- the checks of the declared refinements, exactly as the direct
-- self-reference of T2301 does. See
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2301

module T2301Mutual where

data L a = Nil | Cons a (L a)

{-@ reflect listSum @-}
{-@ listSum :: L Nat -> Nat @-}
listSum :: L Int -> Int
listSum Nil         = 0
listSum (Cons h t)  = h + listSum t

{-@ lazy aa @-}
{-@ reflect aa @-}
{-@ aa :: {l:L Nat | listSum l < 5} @-}
aa :: L Int
aa = Cons 1 bb

{-@ lazy bb @-}
{-@ reflect bb @-}
{-@ bb :: {l:L Nat | listSum l < 5} @-}
bb :: L Int
bb = Cons 1 aa
