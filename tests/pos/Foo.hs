module Foo where


bar = 0

{-@ assume (GHC.List.++) :: [a] -> [a] -> [a] @-}
