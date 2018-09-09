module Foo where

bar = 0

{-@ assume (GHC.Base.++) :: [a] -> [a] -> [a] @-}
