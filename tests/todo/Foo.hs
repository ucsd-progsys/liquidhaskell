{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module Foo where

import Prelude hiding (map, reverse)


baz :: Int
baz = 1

{-@ poo :: ListN Int 1 @-}
poo = [baz, baz]

reverse :: [a] -> [a]

{-@ measure size @-}
size :: [a] -> Int
size []     = 0
size (_:xs) = size xs + 1

{-@ type List  a    = [a]                    @-}
{-@ type ListN a N  = {v:[a] | size v == N } @-}
{-@ type ListX a Xs = ListN a {size Xs}      @-}

{-@ reverse :: xs:List a -> ListN a {size xs} @-}
reverse           = go []
  where
    {-@ go :: acc:_ -> xs:_ -> ListN a {1 + size acc + size xs} @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
