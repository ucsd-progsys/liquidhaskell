-- | Tests that inlines are expanded when used in the bodies
-- of other inlines.
module NestedInlines where

{-@ inline foo @-}
foo :: Int -> Int
foo x = x + 1

{-@ inline bar @-}
bar :: Int -> Bool
bar x = foo x == 1

{-@ mo :: x:Int -> { bar x == bar x } @-}
mo :: Int -> ()
mo _ = ()
