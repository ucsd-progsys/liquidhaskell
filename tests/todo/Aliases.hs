module Foo where

{-@ type Foos = [Foo] @-}

{-@ type Foo = {v:Int | vv > 0} @-}

foo :: [Int]
{-@ foo :: Foos @-}
foo = []
