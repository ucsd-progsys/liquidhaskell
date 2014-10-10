module Goo where

import Prelude hiding (gcd, mod, map, repeat, take)
import Language.Haskell.Liquid.Prelude

map   :: (a -> b) -> List a -> List b



data List a = N | C a (List a)

{-@ map :: (a -> b) -> xs:List a -> List b @-}
map _ N        = N
map f (C x xs) = map f (C x xs) -- f x `C` map f xs

