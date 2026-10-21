{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- A reflected recursive function with arguments that recurses on the very
-- same arguments does not need a nullary equation to trivialize the check of
-- its refinement: the reflected signature of the recursive occurrence embeds
-- the equation rep x = <body>, which rewrites the goal back to the assumed
-- refinement, guarded or not. Checking the body in an environment that only
-- assumes the declared type (extenderTemplate) rejects this. See
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2301

module T2301SameArg where

data L a = Nil | Cons a (L a)

{-@ reflect listSum @-}
{-@ listSum :: L Nat -> Nat @-}
listSum :: L Int -> Int
listSum Nil         = 0
listSum (Cons h t)  = h + listSum t

{-@ lazy rep @-}
{-@ reflect rep @-}
{-@ rep :: x:Nat -> {l:L Nat | listSum l < 5} @-}
rep :: Int -> L Int
rep x = if x > 0 then Cons x (rep x) else Nil
