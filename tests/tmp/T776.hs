{- | There are 2 bugs here, that have to do with `--prune-unsorted`.

     1. Why is the `prod` measure being used in the generic `size`
        function where it doesn't fit?

     2. Why are we getting such a meaningless error message?!

        At the very least some mention of try `prune-unsorted` ?

        Can we not put in a simple check in Bare for now:

        The measure `prod` is not-polymorphic, please run with --prune-unsorted.
        
 -}

{-@ LIQUID "--prune-unsorted" @-}

module LiquidR where

{-@ measure size @-}
size        :: [a] -> Int
size []     = 0
size (_:xs) = 1 + size xs

{-@ measure prod @-}
prod :: [Int] -> Int
prod []     = 1
prod (x:xs) = x + prod xs
