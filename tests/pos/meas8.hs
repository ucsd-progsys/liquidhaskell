module Meas () where

import Language.Haskell.Liquid.Prelude

{-@ include <len.hquals> @-}

{-@ measure rlen :: [a] -> Int 
    rlen ([])   = {v | v = 0}
    rlen (y:ys) = {v | v = (1 + rlen(ys))}
  @-}

{-@ foo :: a -> {v:[b] | rlen(v) = 0} @-}
foo x = []

{-@ mylen :: xs:[a] -> {v:Int | v = rlen(xs)} @-}
mylen          :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs

{-@ mymap :: (a -> b) -> xs:[a] -> {v:[b] | rlen(v) = rlen(xs)} @-}
mymap f []     = []
mymap f (x:xs) = (f x) : (mymap f xs)

