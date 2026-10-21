{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- A valid refinement of a reflected, non-terminating definition must be
-- accepted: one unfolding step of the definition preserves @listSum l > 5@,
-- so the (coinductive) check succeeds. See
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
{-@ ones :: {l:L Nat | listSum l > 5} @-}
ones :: L Int
ones = Cons 1 ones

-- The reflected binder stays usable in other annotations through its
-- (checked) specification: binding @ones@ brings @listSum ones > 5@ into
-- scope, so the theorem holds without unfolding the definition.
{-@ thm :: () -> { listSum ones > 5 } @-}
thm :: () -> ()
thm _ = let _l = ones in ()
