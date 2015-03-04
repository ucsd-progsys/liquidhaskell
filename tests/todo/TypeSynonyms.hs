{-# LANGUAGE DataKinds #-} -- Type level straings
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

module Foo where
import GHC.TypeLits

{-@ foo :: x:Int -> {v:Int | v > x } @-}

foo :: x  ::: Int -> (v ::: Int || v > x) 
bar :: xs ::: [a] -> (v ::: Int || v == length xs)



bar xs = length xs
foo x = x + 1

infixr 7 :::
infixr 6 ||

type x ::: t = t
type t || p  = t
type x > y   = Bool
type x == y   = Bool
-- type (x :: Symbol) > (y :: Symbol)   = Bool

