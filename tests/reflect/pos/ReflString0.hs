
-- cf https://github.com/ucsd-progsys/liquidhaskell/issues/1044

module ReflString0 where

{-@ reflect foo @-}
{-@ foo :: x:_ -> {v:_ | v <=> x == "cat"} @-}
foo :: String -> Bool
foo x = x == "cat"

