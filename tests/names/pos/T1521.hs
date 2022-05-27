module T1521 where

-- https://github.com/ucsd-progsys/liquidhaskell/issues/1521

data Foo = Bool

{-@ measure bar :: Int -> Bool @-}

main :: IO ()
main = pure ()
