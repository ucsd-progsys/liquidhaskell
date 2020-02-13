-- https://github.com/ucsd-progsys/liquidhaskell/issues/1521

data Foo = Bool

{-@ measure bar :: Int -> Bool @-}

main = pure ()
