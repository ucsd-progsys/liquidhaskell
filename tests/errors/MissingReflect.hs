{-@ LIQUID "--expect-error-containing=Illegal type specification for `MissingReflect.empty_foo`" @-}
{-@ LIQUID "--reflection"                     @-}
{-@ LIQUID "--ple"                                @-}

module MissingReflect where

import Language.Haskell.Liquid.ProofCombinators 

-- | This fails with an error as `foo` is unbound sans the `reflect` annotation. 

{- reflect foo -}

{-@ foo  :: Nat ->  xs: [Nat] -> Nat -> Bool / [len xs ]@-}
foo :: Int ->  [Int] -> Int -> Bool
foo lo [] hi     = (lo<=hi)
foo lo (x:xs) hi = (lo<=hi) && foo lo xs x

{-@ empty_foo :: lo:Nat -> hi:{Nat | lo <= hi } -> {foo lo [] hi} @-}
empty_foo :: Int -> Int -> Proof
empty_foo lo hi = (foo lo [] hi) ==. (lo <= hi) ==.True  *** QED

main :: IO ()
main = pure ()
