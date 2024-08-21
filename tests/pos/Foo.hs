module Foo where

bar = 0

{-@ assume (GHC.Internal.Base.++) :: [a] -> [a] -> [a] @-}
