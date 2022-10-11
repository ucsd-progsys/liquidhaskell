{-@ LIQUID "--expect-error-containing=Illegal type specification for `HigherOrderBinder.foo`" @-}
module HigherOrderBinder where

{-@ foo :: a: Int -> f: (Int -> Int) -> {v : Int | v = 123 + (f a) } @-}
foo :: Int -> (Int -> Int) -> Int
foo a f = f a

main :: IO ()
main = pure ()
