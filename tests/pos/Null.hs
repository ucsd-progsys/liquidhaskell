module Null where

foo :: [a] -> [a]
foo xs = if null xs then [] else tail xs
